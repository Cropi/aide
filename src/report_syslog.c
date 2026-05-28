/*
 * AIDE (Advanced Intrusion Detection Environment)
 *
 * Copyright (C) 2025 Hannes von Haugwitz
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */

#include "config.h"
#include "aide.h"
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include "attributes.h"
#include "base64.h"
#include "db.h"
#include "db_line.h"
#include "hashsum.h"
#include "report.h"
#include "report_syslog.h"
#include "seltree.h"
#include "seltree_struct.h"
#include "tree.h"
#include "util.h"

/* Returns the compact syslog file-type prefix, or NULL when mode is unknown
 * (mode & S_IFMT == 0), in which case callers omit the "type=" prefix. */
static const char *get_syslog_type_prefix(mode_t mode) {
    switch (mode & S_IFMT) {
        case S_IFREG:  return "file";
        case S_IFDIR:  return "dir";
        case S_IFLNK:  return "link";
        case S_IFBLK:  return "blockd";
        case S_IFCHR:  return "chard";
#ifdef S_IFIFO
        case S_IFIFO:  return "fifo";
#endif
#ifdef S_IFSOCK
        case S_IFSOCK: return "socket";
#endif
        case 0:        return NULL;
        default:       return "unknown";
    }
}

/* Returns the key name for attribute a.  attr_sizeg is the only exception:
 * its details_string is "Size (>)" which contains '>', so we substitute
 * "Size" to match the original patch's explicit details_string[] change. */
static const char *get_attr_key(ATTRIBUTE a) {
    if (a == attr_sizeg) {
        return "Size";
    }
    return attributes[a].details_string;
}

#ifdef WITH_XATTR

#define SYSLOG_PRINTABLE_XATTR_VALS \
    "0123456789" \
    "abcdefghijklmnopqrstuvwxyz" \
    "ABCDEFGHIJKLMNOPQRSTUVWXYZ" \
    ".-_:;,[]{}<>()!@#$%^&*|\\/?~"

/* Appends one side's xattr values to stream in compact syslog format.
 * Format: ;XAttrs_<side>=|[1]key=val|[2]key=val| */
static void build_xattrs_compact(FILE *stream, db_line *line, const char *side) {
    xattrs_type *xattrs = line ? line->xattrs : NULL;

    if (!xattrs || xattrs->num == 0) {
        fprintf(stream, ";XAttrs_%s=|num=0|", side);
        return;
    }

    fprintf(stream, ";XAttrs_%s=|num=%zu|", side, xattrs->num);

    for (size_t i = 0; i < xattrs->num; i++) {
        const char *key = xattrs->ents[i].key;
        const char *val = (const char *)xattrs->ents[i].val;
        size_t vsz = xattrs->ents[i].vsz;

        /* Check printability (replicates xstrnspn logic from report.c). */
        size_t plen = 0;
        while (plen < vsz && strchr(SYSLOG_PRINTABLE_XATTR_VALS, val[plen]))
            plen++;
        bool printable = (plen == vsz) || (plen == vsz - 1 && val[plen] == '\0');

        if (printable) {
            fprintf(stream, "[%zu]%s=%s|", i + 1, key, val);
        } else {
            char *b64 = encode_base64((byte *)xattrs->ents[i].val, vsz);
            fprintf(stream, "[%zu]%s<=>%s|", i + 1, key, b64 ? b64 : "");
            free(b64);
        }
    }
}
#endif /* WITH_XATTR */

#ifdef WITH_POSIX_ACL
/* Appends one side's ACL to stream in compact syslog format.
 * Format: ;ACL_<side>=A:<acl_a_newlines_as_spaces>|D:<acl_d_newlines_as_spaces>
 *
 * Both A and D are initialized to "<NONE>" before the conditionals, fixing
 * the uninitialized-pointer bug in the original 0.16 patch. */
static void build_acl_compact(FILE *stream, db_line *line, const char *side) {
    acl_type *acl = line ? line->acl : NULL;

    const char *A = "<NONE>";
    const char *D = "<NONE>";
    if (acl) {
        if (acl->acl_a) { A = acl->acl_a; }
        if (acl->acl_d) { D = acl->acl_d; }
    }

    /* Write A component, replacing newlines with spaces. */
    fprintf(stream, ";ACL_%s=A:", side);
    for (const char *p = A; *p; p++) {
        fputc(*p == '\n' ? ' ' : *p, stream);
    }

    /* Write D component, replacing newlines with spaces. */
    fprintf(stream, "|D:");
    for (const char *p = D; *p; p++) {
        fputc(*p == '\n' ? ' ' : *p, stream);
    }
}
#endif /* WITH_POSIX_ACL */

/* Assembles a complete syslog line for one file event into *out.
 *
 * Invariant: this function never calls report_printf(). The caller emits
 * the result with exactly one report_printf() call to avoid fragmenting
 * syslog messages (each report_printf to url_syslog calls vsyslog() once).
 *
 * Cases:
 *   oline != NULL && nline != NULL  → changed entry
 *   oline == NULL                   → added entry
 *   nline == NULL                   → removed entry
 *
 * *out is heap-allocated by open_memstream; caller must free() it. */
static void build_syslog_line(report_t *report, db_line *oline, db_line *nline,
                              DB_ATTR_TYPE attrs, char **out) {
    db_line *ref = nline ? nline : oline;
    const char *type = get_syslog_type_prefix(ref->perm);

    char *buf = NULL;
    size_t bufsz = 0;
    FILE *stream = open_memstream(&buf, &bufsz);

    /* Write "type=path" prefix. */
    if (type) {
        fprintf(stream, "%s=%s", type, ref->filename);
    } else {
        fprintf(stream, "%s", ref->filename);
    }

    if (oline && nline) {
        /* Changed entry: emit only differing attributes. */
        for (int j = 0; j < report_attrs_order_length; j++) {
            ATTRIBUTE a = report_attrs_order[j];

            switch (a) {
                case attr_allhashsums:
                    /* Expand to each compiled-in hash, mirroring print_dbline_attrs(). */
                    for (int i = 0; i < num_hashes; i++) {
                        if (!(ATTR(hashsums[i].attribute) & attrs)) { continue; }
                        const char *key = get_attr_key(hashsums[i].attribute);
                        if (!key) { continue; }
                        char **oval = NULL, **nval = NULL;
                        get_attribute_values(ATTR(hashsums[i].attribute), oline, &oval, report);
                        get_attribute_values(ATTR(hashsums[i].attribute), nline, &nval, report);
                        fprintf(stream, ";%s_old=%s;%s_new=%s",
                                key, oval ? oval[0] : "", key, nval ? nval[0] : "");
                        if (oval) { free(oval[0]); free(oval); }
                        if (nval) { free(nval[0]); free(nval); }
                    }
                    break;

                case attr_size:
                    /* attr_size and attr_sizeg share this slot in report_attrs_order. */
                    if (ATTR(attr_size) & attrs) {
                        const char *key = get_attr_key(attr_size);
                        if (key) {
                            char **oval = NULL, **nval = NULL;
                            get_attribute_values(ATTR(attr_size), oline, &oval, report);
                            get_attribute_values(ATTR(attr_size), nline, &nval, report);
                            fprintf(stream, ";%s_old=%s;%s_new=%s",
                                    key, oval ? oval[0] : "", key, nval ? nval[0] : "");
                            if (oval) { free(oval[0]); free(oval); }
                            if (nval) { free(nval[0]); free(nval); }
                        }
                    }
                    if (ATTR(attr_sizeg) & attrs) {
                        const char *key = get_attr_key(attr_sizeg); /* returns "Size" */
                        if (key) {
                            char **oval = NULL, **nval = NULL;
                            get_attribute_values(ATTR(attr_sizeg), oline, &oval, report);
                            get_attribute_values(ATTR(attr_sizeg), nline, &nval, report);
                            fprintf(stream, ";%s_old=%s;%s_new=%s",
                                    key, oval ? oval[0] : "", key, nval ? nval[0] : "");
                            if (oval) { free(oval[0]); free(oval); }
                            if (nval) { free(nval[0]); free(nval); }
                        }
                    }
                    break;

                default:
                    if (!(ATTR(a) & attrs)) { break; }
#ifdef WITH_XATTR
                    if (a == attr_xattrs) {
                        build_xattrs_compact(stream, oline, "old");
                        build_xattrs_compact(stream, nline, "new");
                        break;
                    }
#endif
#ifdef WITH_POSIX_ACL
                    if (a == attr_acl) {
                        build_acl_compact(stream, oline, "old");
                        build_acl_compact(stream, nline, "new");
                        break;
                    }
#endif
                    {
                        const char *key = get_attr_key(a);
                        if (!key) { break; }
                        char **oval = NULL, **nval = NULL;
                        get_attribute_values(ATTR(a), oline, &oval, report);
                        get_attribute_values(ATTR(a), nline, &nval, report);
                        fprintf(stream, ";%s_old=%s;%s_new=%s",
                                key, oval ? oval[0] : "", key, nval ? nval[0] : "");
                        if (oval) { free(oval[0]); free(oval); }
                        if (nval) { free(nval[0]); free(nval); }
                    }
                    break;
            }
        }
    } else if (!oline) {
        fprintf(stream, "; added");
    } else {
        fprintf(stream, "; removed");
    }

    fclose(stream);
    *out = buf;
}

/* Emits exactly one syslog line for a file event. */
static void emit_syslog_entry(report_t *report, db_line *oline, db_line *nline,
                              DB_ATTR_TYPE attrs) {
    char *line = NULL;
    build_syslog_line(report, oline, nline, attrs, &line);
    report_printf(report, "%s\n", line);
    free(line);
}

/* Unconditional tree walker — does not gate added/removed on report->level,
 * matching the original patch's print_syslog_format() behavior. */
static void syslog_walk_tree(report_t *report, seltree *node) {
    pthread_rwlock_rdlock(&node->rwlock);

    if (node->checked & NODE_CHANGED) {
        emit_syslog_entry(report, node->old_data, node->new_data,
                          get_report_attributes(node, report));
    }
    if (node->checked & NODE_ADDED) {
        emit_syslog_entry(report, NULL, node->new_data,
                          node->new_data->attr & ~report->ignore_added_attrs);
    }
    if (node->checked & NODE_REMOVED) {
        emit_syslog_entry(report, node->old_data, NULL,
                          node->old_data->attr & ~report->ignore_removed_attrs);
    }

    for (tree_node *x = tree_walk_first(node->children); x != NULL; x = tree_walk_next(x)) {
        syslog_walk_tree(report, tree_get_data(x));
    }

    pthread_rwlock_unlock(&node->rwlock);
}

/* ── Module callbacks ─────────────────────────────────────────────────── */

static void noop_header(report_t *report)                            { (void)report; }
static void noop_footer(report_t *report)                            { (void)report; }
static void noop_databases(report_t *report)                         { (void)report; }
static void noop_config_options(report_t *report)                    { (void)report; }
static void noop_report_options(report_t *report)                    { (void)report; }
static void noop_starttime_version(report_t *r, const char *t, const char *v) { (void)r; (void)t; (void)v; }
static void noop_endtime_runtime(report_t *r, const char *t, long rt)         { (void)r; (void)t; (void)rt; }
static void noop_new_database_written(report_t *report)              { (void)report; }
static void noop_entries(report_t *r, seltree *n, const int f)       { (void)r; (void)n; (void)f; }
static void noop_diff_attrs(report_t *report)                        { (void)report; }
static void noop_summary(report_t *report)                           { (void)report; }

/* Emits header + summary when there are differences.  Two separate
 * report_printf() calls — each becomes one syslog message. */
static void syslog_outline(report_t *report) {
    if (report->nadd || report->nrem || report->nchg) {
        report_printf(report, "AIDE found differences between database and filesystem!!\n");
        report_printf(report,
                      "summary;total_number_of_files=%ld;added_files=%ld;"
                      "removed_files=%ld;changed_files=%ld\n",
                      report->ntotal, report->nadd, report->nrem, report->nchg);
    }
}

static void syslog_details(report_t *report, seltree *node) {
    syslog_walk_tree(report, node);
}

report_format_module report_module_syslog = {
    .print_report_config_options     = noop_config_options,
    .print_report_databases          = noop_databases,
    .print_report_details            = syslog_details,
    .print_report_diff_attrs_entries = noop_diff_attrs,
    .print_report_endtime_runtime    = noop_endtime_runtime,
    .print_report_entries            = noop_entries,
    .print_report_footer             = noop_footer,
    .print_report_header             = noop_header,
    .print_report_new_database_written = noop_new_database_written,
    .print_report_outline            = syslog_outline,
    .print_report_report_options     = noop_report_options,
    .print_report_starttime_version  = noop_starttime_version,
    .print_report_summary            = noop_summary,
};
