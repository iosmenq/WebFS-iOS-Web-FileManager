/*
 * webfs.c
 * Codded by iosmen (c) 2025
 * WebFS - Minimal HTTP file manager for jailbroken iOS
 * - Single-file C program (POSIX sockets + pthread)
 * - Mini white HTML UI embedded
 * - Actions: browse, download, upload (PUT), mkdir, delete
 * - Optional Basic Auth: -u user -P pass
 *
 * Build:
 *   clang -O2 -Wall -pthread -o webfs webfs.c
 *
 * Run:
 *   sudo webfs -p 8000 -r /
 *
 * WARNING: Running as root exposes the filesystem. Use on trusted networks.
 *
 * Version: 0.549 --Alpha
 */

#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>    
#include <ctype.h>
#include <stdarg.h>
#include <unistd.h>
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <dirent.h>
#include <time.h>
#include <stdint.h>
#include <limits.h>

#define BACKLOG 10
#define BUFSIZE 8192

static int g_port = 8080;
static char g_root[PATH_MAX] = "/";
static char g_user[128] = {0};
static char g_pass[128] = {0};
static int g_auth_enabled = 0;

/* ---------- Utilities ---------- */

static void fatal(const char *fmt, ...) {
    va_list ap; va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    exit(1);
}

/* Quick heuristic for jailbreak environment */
static int is_jailbroken(void) {
    if (access("/Applications/Cydia.app", F_OK) == 0) return 1;
    if (access("/usr/sbin/sshd", F_OK) == 0) return 1;
    if (geteuid() == 0) return 1;
    return 0;
}

/* URL-decode (dst must be large enough) */
static void url_decode(char *dst, const char *src) {
    while (*src) {
        if (*src == '%' && isxdigit((unsigned char)src[1]) && isxdigit((unsigned char)src[2])) {
            char hex[3] = { src[1], src[2], 0 };
            *dst++ = (char)strtol(hex, NULL, 16);
            src += 3;
        } else if (*src == '+') {
            *dst++ = ' ';
            src++;
        } else {
            *dst++ = *src++;
        }
    }
    *dst = '\0';
}

/* Build sanitized filesystem path: join root + requested path and collapse .. */
static void join_path(char *out, size_t outsz, const char *root, const char *reqpath) {
    char decoded[PATH_MAX];
    url_decode(decoded, reqpath ? reqpath : "/");
    char *q = strchr(decoded, '?'); if (q) *q = '\0';
    const char *p = decoded;
    if (p[0] == '/') p++;
    char tmp[PATH_MAX];
    snprintf(tmp, sizeof(tmp), "%s/%s", root && root[0] ? root : "/", p);
    /* collapse .. and . */
    char outbuf[PATH_MAX] = {0};
    char *token, *saveptr;
    token = strtok_r(tmp, "/", &saveptr);
    while (token) {
        if (strcmp(token, "..") == 0) {
            char *last = strrchr(outbuf, '/');
            if (last) *last = '\0';
        } else if (strcmp(token, ".") != 0 && token[0] != 0) {
            if (outbuf[0] == '\0') snprintf(outbuf + strlen(outbuf), sizeof(outbuf)-strlen(outbuf), "%s", token);
            else snprintf(outbuf + strlen(outbuf), sizeof(outbuf)-strlen(outbuf), "/%s", token);
        }
        token = strtok_r(NULL, "/", &saveptr);
    }
    if (outbuf[0] == '\0') strncpy(out, "/", outsz);
    else {
        if (root && root[0] == '/') {
            char tmp2[PATH_MAX];
            if (outbuf[0] == '/') snprintf(tmp2, sizeof(tmp2), "%s", outbuf);
            else snprintf(tmp2, sizeof(tmp2), "/%s", outbuf);
            strncpy(out, tmp2, outsz);
        } else {
            strncpy(out, outbuf, outsz);
        }
    }
}

/* Simple base64 decode for Basic Auth */
static int b64val(char c) {
    if (c >= 'A' && c <= 'Z') return c - 'A';
    if (c >= 'a' && c <= 'z') return c - 'a' + 26;
    if (c >= '0' && c <= '9') return c - '0' + 52;
    if (c == '+') return 62;
    if (c == '/') return 63;
    return -1;
}
static int b64dec_simple(const char *in, char *out, int outlen) {
    int accum = 0, bits = 0, o = 0;
    for (size_t i = 0; in[i] && o < outlen-1; ++i) {
        int v = b64val(in[i]);
        if (v < 0) continue;
        accum = (accum << 6) | v;
        bits += 6;
        if (bits >= 8) {
            bits -= 8;
            out[o++] = (accum >> bits) & 0xFF;
        }
    }
    out[o] = '\0';
    return o;
}

/* Safe send-all */
static ssize_t send_all(int fd, const void *buf, size_t sz) {
    size_t sent = 0;
    const char *p = buf;
    while (sent < sz) {
        ssize_t r = send(fd, p + sent, sz - sent, 0);
        if (r <= 0) return r;
        sent += r;
    }
    return (ssize_t)sent;
}

/* Send HTTP headers */
static void send_headers(int fd, int code, const char *status, const char *ctype, size_t content_len, const char *extra) {
    char hdr[1024];
    int n = snprintf(hdr, sizeof(hdr),
                     "HTTP/1.1 %d %s\r\n"
                     "Server: WebFS/0.1\r\n"
                     "Connection: close\r\n"
                     "Content-Length: %zu\r\n",
                     code, status, content_len);
    send_all(fd, hdr, n);
    if (ctype) {
        char t[128];
        int m = snprintf(t, sizeof(t), "Content-Type: %s\r\n", ctype);
        send_all(fd, t, m);
    }
    if (extra) send_all(fd, extra, strlen(extra));
    send_all(fd, "\r\n", 2);
}

/* Custom strcasestr implementation */
static char* my_strcasestr(const char* haystack, const char* needle) {
    if (!haystack || !needle) return NULL;
    
    for (; *haystack; haystack++) {
        const char* h = haystack;
        const char* n = needle;
        
        while (*h && *n && tolower((unsigned char)*h) == tolower((unsigned char)*n)) {
            h++;
            n++;
        }
        
        if (*n == '\0') {
            return (char*)haystack;
        }
    }
    
    return NULL;
}

/* ---------- Embedded UI (Advanced white interface) ---------- */

static const char *INDEX_HTML =
"<!DOCTYPE html>\n"
"<html lang=\"tr\">\n"
"<head>\n"
"  <meta charset=\"UTF-8\">\n"
"  <meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n"
"  <link rel=\"apple-touch-icon\" sizes=\"128x128\" href=\"https://webfs-header-icons.netlify.app/ios/apple/asset/apple@x128.ico\">\n"
"  <link rel=\"icon\" type=\"image/png\" sizes=\"64x64\" href=\"https://webfs-header-icons.netlify.app/ios/apple/asset/webfs.ico\">\n"
"  <title>WebFS - FileManager</title>\n"
"  <style>\n"
"    :root {\n"
"      --primary: #0a84ff;\n"
"      --primary-dark: #0066cc;\n"
"      --secondary: #6c757d;\n"
"      --success: #28a745;\n"
"      --danger: #dc3545;\n"
"      --warning: #ffc107;\n"
"      --light: #f8f9fa;\n"
"      --dark: #343a40;\n"
"      --white: #ffffff;\n"
"      --gray-100: #f8f9fa;\n"
"      --gray-200: #e9ecef;\n"
"      --gray-300: #dee2e6;\n"
"      --gray-400: #ced4da;\n"
"      --gray-500: #adb5bd;\n"
"      --gray-600: #6c757d;\n"
"      --gray-700: #495057;\n"
"      --gray-800: #343a40;\n"
"      --gray-900: #212529;\n"
"      --border-radius: 8px;\n"
"      --box-shadow: 0 4px 6px rgba(0, 0, 0, 0.1);\n"
"      --transition: all 0.3s ease;\n"
"    }\n"
"\n"
"    * {\n"
"      margin: 0;\n"
"      padding: 0;\n"
"      box-sizing: border-box;\n"
"    }\n"
"\n"
"    body {\n"
"      font-family: 'Segoe UI', system-ui, -apple-system, sans-serif;\n"
"      background-color: var(--white);\n"
"      color: var(--gray-800);\n"
"      line-height: 1.6;\n"
"    }\n"
"\n"
"    .app-container {\n"
"      display: flex;\n"
"      min-height: 100vh;\n"
"    }\n"
"\n"
"    /* Sidebar Styles */\n"
"    .sidebar {\n"
"      width: 250px;\n"
"      background-color: var(--white);\n"
"      border-right: 1px solid var(--gray-300);\n"
"      display: flex;\n"
"      flex-direction: column;\n"
"    }\n"
"\n"
"    .sidebar-header {\n"
"      padding: 20px;\n"
"      border-bottom: 1px solid var(--gray-300);\n"
"    }\n"
"\n"
"    .sidebar-header h1 {\n"
"      font-size: 1.5rem;\n"
"      font-weight: 700;\n"
"      color: var(--primary);\n"
"      display: flex;\n"
"      align-items: center;\n"
"      gap: 10px;\n"
"    }\n"
"\n"
"    .sidebar-nav {\n"
"      padding: 20px 0;\n"
"      flex-grow: 1;\n"
"    }\n"
"\n"
"    .nav-item {\n"
"      display: flex;\n"
"      align-items: center;\n"
"      padding: 12px 20px;\n"
"      color: var(--gray-700);\n"
"      text-decoration: none;\n"
"      transition: var(--transition);\n"
"      border: none;\n"
"      background: none;\n"
"      width: 100%;\n"
"      text-align: left;\n"
"      cursor: pointer;\n"
"    }\n"
"\n"
"    .nav-item:hover {\n"
"      background-color: var(--gray-100);\n"
"      color: var(--primary);\n"
"    }\n"
"\n"
"    .nav-item.active {\n"
"      background-color: var(--primary);\n"
"      color: var(--white);\n"
"    }\n"
"\n"
"    .nav-icon {\n"
"      margin-right: 10px;\n"
"      width: 20px;\n"
"      text-align: center;\n"
"    }\n"
"\n"
"    .sidebar-footer {\n"
"      padding: 20px;\n"
"      border-top: 1px solid var(--gray-300);\n"
"      font-size: 0.85rem;\n"
"      color: var(--gray-600);\n"
"    }\n"
"\n"
"    /* Main Content Styles */\n"
"    .main-content {\n"
"      flex: 1;\n"
"      display: flex;\n"
"      flex-direction: column;\n"
"      overflow: hidden;\n"
"    }\n"
"\n"
"    .topbar {\n"
"      padding: 15px 20px;\n"
"      background-color: var(--white);\n"
"      border-bottom: 1px solid var(--gray-300);\n"
"      display: flex;\n"
"      justify-content: space-between;\n"
"      align-items: center;\n"
"    }\n"
"\n"
"    .breadcrumb {\n"
"      display: flex;\n"
"      align-items: center;\n"
"      font-size: 0.9rem;\n"
"    }\n"
"\n"
"    .breadcrumb a {\n"
"      color: var(--gray-600);\n"
"      text-decoration: none;\n"
"      cursor: pointer;\n"
"    }\n"
"\n"
"    .breadcrumb a:hover {\n"
"      color: var(--primary);\n"
"    }\n"
"\n"
"    .breadcrumb-separator {\n"
"      margin: 0 8px;\n"
"      color: var(--gray-500);\n"
"    }\n"
"\n"
"    .user-actions {\n"
"      display: flex;\n"
"      gap: 10px;\n"
"    }\n"
"\n"
"    .btn {\n"
"      padding: 8px 16px;\n"
"      border-radius: var(--border-radius);\n"
"      border: none;\n"
"      font-weight: 500;\n"
"      cursor: pointer;\n"
"      transition: var(--transition);\n"
"      display: inline-flex;\n"
"      align-items: center;\n"
"      gap: 6px;\n"
"    }\n"
"\n"
"    .btn-primary {\n"
"      background-color: var(--primary);\n"
"      color: var(--white);\n"
"    }\n"
"\n"
"    .btn-primary:hover {\n"
"      background-color: var(--primary-dark);\n"
"    }\n"
"\n"
"    .btn-outline {\n"
"      background-color: transparent;\n"
"      border: 1px solid var(--gray-400);\n"
"      color: var(--gray-700);\n"
"    }\n"
"\n"
"    .btn-outline:hover {\n"
"      background-color: var(--gray-100);\n"
"    }\n"
"\n"
"    .content-area {\n"
"      flex: 1;\n"
"      padding: 20px;\n"
"      overflow-y: auto;\n"
"    }\n"
"\n"
"    /* Toolbar Styles */\n"
"    .toolbar {\n"
"      display: flex;\n"
"      justify-content: space-between;\n"
"      margin-bottom: 20px;\n"
"      padding-bottom: 15px;\n"
"      border-bottom: 1px solid var(--gray-300);\n"
"    }\n"
"\n"
"    .toolbar-left {\n"
"      display: flex;\n"
"      gap: 10px;\n"
"    }\n"
"\n"
"    .toolbar-right {\n"
"      display: flex;\n"
"      gap: 10px;\n"
"    }\n"
"\n"
"    .search-box {\n"
"      position: relative;\n"
"      width: 300px;\n"
"    }\n"
"\n"
"    .search-box input {\n"
"      width: 100%;\n"
"      padding: 10px 15px 10px 40px;\n"
"      border: 1px solid var(--gray-400);\n"
"      border-radius: var(--border-radius);\n"
"      font-size: 0.9rem;\n"
"    }\n"
"\n"
"    .search-icon {\n"
"      position: absolute;\n"
"      left: 15px;\n"
"      top: 50%;\n"
"      transform: translateY(-50%);\n"
"      color: var(--gray-500);\n"
"    }\n"
"\n"
"    .view-toggle {\n"
"      display: flex;\n"
"      border: 1px solid var(--gray-400);\n"
"      border-radius: var(--border-radius);\n"
"      overflow: hidden;\n"
"    }\n"
"\n"
"    .view-toggle button {\n"
"      padding: 8px 12px;\n"
"      background: var(--white);\n"
"      border: none;\n"
"      cursor: pointer;\n"
"      transition: var(--transition);\n"
"    }\n"
"\n"
"    .view-toggle button.active {\n"
"      background-color: var(--gray-200);\n"
"    }\n"
"\n"
"    /* File Listing Styles */\n"
"    .file-listing {\n"
"      background-color: var(--white);\n"
"      border-radius: var(--border-radius);\n"
"      box-shadow: var(--box-shadow);\n"
"      overflow: hidden;\n"
"    }\n"
"\n"
"    .file-header {\n"
"      display: grid;\n"
"      grid-template-columns: 3fr 1fr 1fr 1fr;\n"
"      padding: 15px 20px;\n"
"      background-color: var(--gray-100);\n"
"      border-bottom: 1px solid var(--gray-300);\n"
"      font-weight: 600;\n"
"      color: var(--gray-700);\n"
"    }\n"
"\n"
"    .file-rows {\n"
"      max-height: 500px;\n"
"      overflow-y: auto;\n"
"    }\n"
"\n"
"    .file-row {\n"
"      display: grid;\n"
"      grid-template-columns: 3fr 1fr 1fr 1fr;\n"
"      padding: 12px 20px;\n"
"      border-bottom: 1px solid var(--gray-200);\n"
"      align-items: center;\n"
"      transition: var(--transition);\n"
"    }\n"
"\n"
"    .file-row:hover {\n"
"      background-color: var(--gray-100);\n"
"    }\n"
"\n"
"    .file-name {\n"
"      display: flex;\n"
"      align-items: center;\n"
"      gap: 10px;\n"
"    }\n"
"\n"
"    .file-icon {\n"
"      width: 24px;\n"
"      height: 24px;\n"
"      display: flex;\n"
"      align-items: center;\n"
"      justify-content: center;\n"
"      color: var(--gray-600);\n"
"    }\n"
"\n"
"    .file-actions {\n"
"      display: flex;\n"
"      gap: 8px;\n"
"    }\n"
"\n"
"    .action-btn {\n"
"      background: none;\n"
"      border: none;\n"
"      color: var(--gray-600);\n"
"      cursor: pointer;\n"
"      transition: var(--transition);\n"
"      padding: 5px;\n"
"      border-radius: 4px;\n"
"      display: flex;\n"
"      align-items: center;\n"
"      justify-content: center;\n"
"    }\n"
"\n"
"    .action-btn:hover {\n"
"      background-color: var(--gray-200);\n"
"      color: var(--gray-800);\n"
"    }\n"
"\n"
"    .action-btn:disabled {\n"
"      opacity: 0.5;\n"
"      cursor: not-allowed;\n"
"    }\n"
"\n"
"    /* Stats Section */\n"
"    .stats-section {\n"
"      display: grid;\n"
"      grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));\n"
"      gap: 20px;\n"
"      margin-bottom: 30px;\n"
"    }\n"
"\n"
"    .stat-card {\n"
"      background-color: var(--white);\n"
"      border-radius: var(--border-radius);\n"
"      box-shadow: var(--box-shadow);\n"
"      padding: 20px;\n"
"      display: flex;\n"
"      align-items: center;\n"
"      gap: 15px;\n"
"    }\n"
"\n"
"    .stat-icon {\n"
"      width: 50px;\n"
"      height: 50px;\n"
"      border-radius: 50%;\n"
"      display: flex;\n"
"      align-items: center;\n"
"      justify-content: center;\n"
"      font-size: 1.5rem;\n"
"    }\n"
"\n"
"    .stat-icon.primary {\n"
"      background-color: rgba(10, 132, 255, 0.1);\n"
"      color: var(--primary);\n"
"    }\n"
"\n"
"    .stat-icon.success {\n"
"      background-color: rgba(40, 167, 69, 0.1);\n"
"      color: var(--success);\n"
"    }\n"
"\n"
"    .stat-icon.warning {\n"
"      background-color: rgba(255, 193, 7, 0.1);\n"
"      color: var(--warning);\n"
"    }\n"
"\n"
"    .stat-icon.danger {\n"
"      background-color: rgba(220, 53, 69, 0.1);\n"
"      color: var(--danger);\n"
"    }\n"
"\n"
"    .stat-info h3 {\n"
"      font-size: 1.5rem;\n"
"      font-weight: 700;\n"
"      margin-bottom: 5px;\n"
"    }\n"
"\n"
"    .stat-info p {\n"
"      color: var(--gray-600);\n"
"      font-size: 0.9rem;\n"
"    }\n"
"\n"
"    /* Modal Styles */\n"
"    .modal-overlay {\n"
"      position: fixed;\n"
"      top: 0;\n"
"      left: 0;\n"
"      right: 0;\n"
"      bottom: 0;\n"
"      background-color: rgba(0, 0, 0, 0.5);\n"
"      display: flex;\n"
"      align-items: center;\n"
"      justify-content: center;\n"
"      z-index: 1000;\n"
"      opacity: 0;\n"
"      visibility: hidden;\n"
"      transition: var(--transition);\n"
"    }\n"
"\n"
"    .modal-overlay.active {\n"
"      opacity: 1;\n"
"      visibility: visible;\n"
"    }\n"
"\n"
"    .modal {\n"
"      background-color: var(--white);\n"
"      border-radius: var(--border-radius);\n"
"      box-shadow: 0 10px 25px rgba(0, 0, 0, 0.2);\n"
"      width: 500px;\n"
"      max-width: 90%;\n"
"      transform: translateY(-20px);\n"
"      transition: var(--transition);\n"
"    }\n"
"\n"
"    .modal-overlay.active .modal {\n"
"      transform: translateY(0);\n"
"    }\n"
"\n"
"    .modal-header {\n"
"      padding: 20px;\n"
"      border-bottom: 1px solid var(--gray-300);\n"
"      display: flex;\n"
"      justify-content: space-between;\n"
"      align-items: center;\n"
"    }\n"
"\n"
"    .modal-title {\n"
"      font-size: 1.2rem;\n"
"      font-weight: 600;\n"
"    }\n"
"\n"
"    .modal-close {\n"
"      background: none;\n"
"      border: none;\n"
"      font-size: 1.2rem;\n"
"      cursor: pointer;\n"
"      color: var(--gray-600);\n"
"    }\n"
"\n"
"    .modal-body {\n"
"      padding: 20px;\n"
"    }\n"
"\n"
"    .form-group {\n"
"      margin-bottom: 15px;\n"
"    }\n"
"\n"
"    .form-group label {\n"
"      display: block;\n"
"      margin-bottom: 5px;\n"
"      font-weight: 500;\n"
"    }\n"
"\n"
"    .form-control {\n"
"      width: 100%;\n"
"      padding: 10px 15px;\n"
"      border: 1px solid var(--gray-400);\n"
"      border-radius: var(--border-radius);\n"
"      font-size: 0.9rem;\n"
"    }\n"
"\n"
"    .modal-footer {\n"
"      padding: 15px 20px;\n"
"      border-top: 1px solid var(--gray-300);\n"
"      display: flex;\n"
"      justify-content: flex-end;\n"
"      gap: 10px;\n"
"    }\n"
"\n"
"    /* File Viewer */\n"
"    .file-viewer {\n"
"      max-height: 400px;\n"
"      overflow: auto;\n"
"      border: 1px solid var(--gray-300);\n"
"      border-radius: var(--border-radius);\n"
"      padding: 15px;\n"
"      background: var(--gray-100);\n"
"      font-family: monospace;\n"
"      white-space: pre-wrap;\n"
"    }\n"
"\n"
"    .file-viewer img {\n"
"      max-width: 100%;\n"
"      height: auto;\n"
"      display: block;\n"
"      margin: 0 auto;\n"
"    }\n"
"\n"
"    .status-message {\n"
"      padding: 10px;\n"
"      margin: 10px 0;\n"
"      border-radius: var(--border-radius);\n"
"      text-align: center;\n"
"      background-color: rgba(40, 167, 69, 0.1);\n"
"      color: var(--success);\n"
"      border: 1px solid var(--success);\n"
"    }\n"
"\n"
"    /* Responsive Styles */\n"
"    @media (max-width: 992px) {\n"
"      .app-container {\n"
"        flex-direction: column;\n"
"      }\n"
"      \n"
"      .sidebar {\n"
"        width: 100%;\n"
"        height: auto;\n"
"      }\n"
"      \n"
"      .sidebar-nav {\n"
"        display: flex;\n"
"        overflow-x: auto;\n"
"        padding: 10px 0;\n"
"      }\n"
"      \n"
"      .nav-item {\n"
"        white-space: nowrap;\n"
"      }\n"
"    }\n"
"\n"
"    @media (max-width: 768px) {\n"
"      .toolbar {\n"
"        flex-direction: column;\n"
"        gap: 15px;\n"
"      }\n"
"      \n"
"      .toolbar-left, .toolbar-right {\n"
"        width: 100%;\n"
"      }\n"
"      \n"
"      .search-box {\n"
"        width: 100%;\n"
"      }\n"
"      \n"
"      .file-header, .file-row {\n"
"        grid-template-columns: 2fr 1fr 1fr;\n"
"      }\n"
"      \n"
"      .file-header .file-type, .file-row .file-type {\n"
"        display: none;\n"
"      }\n"
"    }\n"
"\n"
"    @media (max-width: 576px) {\n"
"      .file-header, .file-row {\n"
"        grid-template-columns: 2fr 1fr;\n"
"      }\n"
"      \n"
"      .file-header .file-size, .file-row .file-size {\n"
"        display: none;\n"
"      }\n"
"      \n"
"      .stats-section {\n"
"        grid-template-columns: 1fr;\n"
"      }\n"
"    }\n"
"  </style>\n"
"</head>\n"
"<body>\n"
"  <div class=\"app-container\">\n"
"    <!-- Sidebar -->\n"
"    <div class=\"sidebar\">\n"
"      <div class=\"sidebar-header\">\n"
"        <h1><span class=\"nav-icon\">📁</span> WebFS</h1>\n"
"      </div>\n"
"      <div class=\"sidebar-nav\">\n"
"        <button class=\"nav-item active\" data-path=\"/\">\n"
"          <span class=\"nav-icon\">🏠</span> Home\n"
"        </button>\n"
"        <button class=\"nav-item\" data-path=\"/var/mobile\">\n"
"          <span class=\"nav-icon\">📱</span> Mobile\n"
"        </button>\n"
"        <button class=\"nav-item\" data-path=\"/var/mobile/Media\">\n"
"          <span class=\"nav-icon\">🖼️</span> Media\n"
"        </button>\n"
"        <button class=\"nav-item\" data-path=\"/Applications\">\n"
"          <span class=\"nav-icon\">📱</span> Applications\n"
"        </button>\n"
"        <button class=\"nav-item\" data-path=\"/usr\">\n"
"          <span class=\"nav-icon\">⚙️</span> System\n"
"        </button>\n"
"        <button class=\"nav-item\" data-path=\"/etc\">\n"
"          <span class=\"nav-icon\">📄</span> Config\n"
"        </button>\n"
"      </div>\n"
"      <div class=\"sidebar-footer\">\n"
"        <p>WebFS</p>\n"
"        <p>iosmen (c) 2025</p>\n"
"      </div>\n"
"    </div>\n"
"\n"
"    <!-- Main Content -->\n"
"    <div class=\"main-content\">\n"
"      <!-- Topbar -->\n"
"      <div class=\"topbar\">\n"
"        <div class=\"breadcrumb\" id=\"breadcrumb\">\n"
"          <a data-path=\"/\">Home</a>\n"
"        </div>\n"
"        <div class=\"user-actions\">\n"
"          <button class=\"btn btn-outline\" id=\"refreshBtn\">\n"
"            <span class=\"nav-icon\">🔄</span> Refresh\n"
"          </button>\n"
"          <button class=\"btn btn-primary\" id=\"uploadBtn\">\n"
"            <span class=\"nav-icon\">📤</span> Upload\n"
"          </button>\n"
"        </div>\n"
"      </div>\n"
"\n"
"      <!-- Content Area -->\n"
"      <div class=\"content-area\">\n"
"        <!-- Stats Section -->\n"
"        <div class=\"stats-section\">\n"
"          <div class=\"stat-card\">\n"
"            <div class=\"stat-icon primary\">\n"
"              <span class=\"nav-icon\">📁</span>\n"
"            </div>\n"
"            <div class=\"stat-info\">\n"
"              <h3 id=\"folderCount\">0</h3>\n"
"              <p>Folders</p>\n"
"            </div>\n"
"          </div>\n"
"          <div class=\"stat-card\">\n"
"            <div class=\"stat-icon success\">\n"
"              <span class=\"nav-icon\">📄</span>\n"
"            </div>\n"
"            <div class=\"stat-info\">\n"
"              <h3 id=\"fileCount\">0</h3>\n"
"              <p>Files</p>\n"
"            </div>\n"
"          </div>\n"
"          <div class=\"stat-card\">\n"
"            <div class=\"stat-icon warning\">\n"
"              <span class=\"nav-icon\">💾</span>\n"
"            </div>\n"
"            <div class=\"stat-info\">\n"
"              <h3 id=\"totalSize\">0 B</h3>\n"
"              <p>Total Size</p>\n"
"            </div>\n"
"          </div>\n"
"          <div class=\"stat-card\">\n"
"            <div class=\"stat-icon danger\">\n"
"              <span class=\"nav-icon\">📊</span>\n"
"            </div>\n"
"            <div class=\"stat-info\">\n"
"              <h3 id=\"itemsCount\">0</h3>\n"
"              <p>Total Items</p>\n"
"            </div>\n"
"          </div>\n"
"        </div>\n"
"\n"
"        <!-- Toolbar -->\n"
"        <div class=\"toolbar\">\n"
"          <div class=\"toolbar-left\">\n"
"            <div class=\"search-box\">\n"
"              <span class=\"search-icon\">🔍</span>\n"
"              <input type=\"text\" id=\"searchInput\" placeholder=\"Search files and folders...\">\n"
"            </div>\n"
"          </div>\n"
"          <div class=\"toolbar-right\">\n"
"            <button class=\"btn btn-outline\" id=\"newFolderBtn\">\n"
"              <span class=\"nav-icon\">📁+</span> New Folder\n"
"            </button>\n"
"            <button class=\"btn btn-outline\" id=\"newFileBtn\">\n"
"              <span class=\"nav-icon\">📄+</span> New File\n"
"            </button>\n"
"          </div>\n"
"        </div>\n"
"\n"
"        <!-- Status Message -->\n"
"        <div id=\"statusMessage\"></div>\n"
"\n"
"        <!-- File Listing -->\n"
"        <div class=\"file-listing\" id=\"fileListing\">\n"
"          <div class=\"file-header\">\n"
"            <div class=\"file-name\">Name</div>\n"
"            <div class=\"file-size\">Size</div>\n"
"            <div class=\"file-type\">Type</div>\n"
"            <div class=\"file-actions\">Actions</div>\n"
"          </div>\n"
"          <div class=\"file-rows\" id=\"fileRows\">\n"
"            <!-- Files will be populated here by JavaScript -->\n"
"          </div>\n"
"        </div>\n"
"      </div>\n"
"    </div>\n"
"  </div>\n"
"\n"
"  <!-- New Folder Modal -->\n"
"  <div class=\"modal-overlay\" id=\"newFolderModal\">\n"
"    <div class=\"modal\">\n"
"      <div class=\"modal-header\">\n"
"        <div class=\"modal-title\">Create New Folder</div>\n"
"        <button class=\"modal-close\" id=\"closeFolderModal\">&times;</button>\n"
"      </div>\n"
"      <div class=\"modal-body\">\n"
"        <div class=\"form-group\">\n"
"          <label for=\"folderName\">Folder Name</label>\n"
"          <input type=\"text\" id=\"folderName\" class=\"form-control\" placeholder=\"Enter folder name\">\n"
"        </div>\n"
"      </div>\n"
"      <div class=\"modal-footer\">\n"
"        <button class=\"btn btn-outline\" id=\"cancelFolderBtn\">Cancel</button>\n"
"        <button class=\"btn btn-primary\" id=\"createFolderBtn\">Create</button>\n"
"      </div>\n"
"    </div>\n"
"  </div>\n"
"\n"
"  <!-- New File Modal -->\n"
"  <div class=\"modal-overlay\" id=\"newFileModal\">\n"
"    <div class=\"modal\">\n"
"      <div class=\"modal-header\">\n"
"        <div class=\"modal-title\">Create New File</div>\n"
"        <button class=\"modal-close\" id=\"closeFileModal\">&times;</button>\n"
"      </div>\n"
"      <div class=\"modal-body\">\n"
"        <div class=\"form-group\">\n"
"          <label for=\"fileName\">File Name</label>\n"
"          <input type=\"text\" id=\"fileName\" class=\"form-control\" placeholder=\"Enter file name\">\n"
"        </div>\n"
"        <div class=\"form-group\">\n"
"          <label for=\"fileContent\">File Content (optional)</label>\n"
"          <textarea id=\"fileContent\" class=\"form-control\" rows=\"6\" placeholder=\"Enter file content\"></textarea>\n"
"        </div>\n"
"      </div>\n"
"      <div class=\"modal-footer\">\n"
"        <button class=\"btn btn-outline\" id=\"cancelFileBtn\">Cancel</button>\n"
"        <button class=\"btn btn-primary\" id=\"createFileBtn\">Create</button>\n"
"      </div>\n"
"    </div>\n"
"  </div>\n"
"\n"
"  <!-- Upload Modal -->\n"
"  <div class=\"modal-overlay\" id=\"uploadModal\">\n"
"    <div class=\"modal\">\n"
"      <div class=\"modal-header\">\n"
"        <div class=\"modal-title\">Upload Files</div>\n"
"        <button class=\"modal-close\" id=\"closeUploadModal\">&times;</button>\n"
"      </div>\n"
"      <div class=\"modal-body\">\n"
"        <div class=\"form-group\">\n"
"          <label for=\"fileUpload\">Select Files</label>\n"
"          <input type=\"file\" id=\"fileUpload\" class=\"form-control\" multiple>\n"
"        </div>\n"
"        <div class=\"upload-progress\" id=\"uploadProgress\">\n"
"          <!-- Progress will be shown here -->\n"
"        </div>\n"
"      </div>\n"
"      <div class=\"modal-footer\">\n"
"        <button class=\"btn btn-outline\" id=\"cancelUploadBtn\">Cancel</button>\n"
"        <button class=\"btn btn-primary\" id=\"startUploadBtn\">Start Upload</button>\n"
"      </div>\n"
"    </div>\n"
"  </div>\n"
"\n"
"  <!-- Rename Modal -->\n"
"  <div class=\"modal-overlay\" id=\"renameModal\">\n"
"    <div class=\"modal\">\n"
"      <div class=\"modal-header\">\n"
"        <div class=\"modal-title\">Rename Item</div>\n"
"        <button class=\"modal-close\" id=\"closeRenameModal\">&times;</button>\n"
"      </div>\n"
"      <div class=\"modal-body\">\n"
"        <div class=\"form-group\">\n"
"          <label for=\"renameName\">New Name</label>\n"
"          <input type=\"text\" id=\"renameName\" class=\"form-control\" placeholder=\"Enter new name\">\n"
"        </div>\n"
"      </div>\n"
"      <div class=\"modal-footer\">\n"
"        <button class=\"btn btn-outline\" id=\"cancelRenameBtn\">Cancel</button>\n"
"        <button class=\"btn btn-primary\" id=\"confirmRenameBtn\">Rename</button>\n"
"      </div>\n"
"    </div>\n"
"  </div>\n"
"\n"
"  <!-- File Viewer Modal -->\n"
"  <div class=\"modal-overlay\" id=\"fileViewerModal\">\n"
"    <div class=\"modal\" style=\"width: 90%; max-width: 1200px;\">\n"
"      <div class=\"modal-header\">\n"
"        <div class=\"modal-title\" id=\"fileViewerTitle\">File Viewer</div>\n"
"        <button class=\"modal-close\" id=\"closeFileViewerModal\">&times;</button>\n"
"      </div>\n"
"      <div class=\"modal-body\">\n"
"        <div class=\"file-viewer\" id=\"fileViewerContent\">\n"
"          <!-- File content will be shown here -->\n"
"        </div>\n"
"      </div>\n"
"      <div class=\"modal-footer\">\n"
"        <button class=\"btn btn-outline\" id=\"closeViewerBtn\">Close</button>\n"
"        <button class=\"btn btn-primary\" id=\"downloadViewerBtn\">Download</button>\n"
"      </div>\n"
"    </div>\n"
"  </div>\n"
"\n"
"  <script>\n"
"    // State management\n"
"    let currentPath = '/';\n"
"    let currentEntries = [];\n"
"    let itemToRename = null;\n"
"    let itemToView = null;\n"
"\n"
"    // Utility functions\n"
"    function formatBytes(bytes) {\n"
"      if (bytes === 0) return '0 B';\n"
"      const k = 1024;\n"
"      const sizes = ['B', 'KB', 'MB', 'GB', 'TB'];\n"
"      const i = Math.floor(Math.log(bytes) / Math.log(k));\n"
"      return parseFloat((bytes / Math.pow(k, i)).toFixed(2)) + ' ' + sizes[i];\n"
"    }\n"
"\n"
"    function getFileIcon(type, name) {\n"
"      if (type === 'dir') return '📁';\n"
"      \n"
"      const ext = name.split('.').pop().toLowerCase();\n"
"      const iconMap = {\n"
"        'pdf': '📕',\n"
"        'doc': '📘', 'docx': '📘',\n"
"        'txt': '📄',\n"
"        'xls': '📊', 'xlsx': '📊', 'csv': '📊',\n"
"        'ppt': '📑', 'pptx': '📑',\n"
"        'jpg': '🖼️', 'jpeg': '🖼️', 'png': '🖼️', 'gif': '🖼️',\n"
"        'mp3': '🎵', 'wav': '🎵',\n"
"        'mp4': '🎥', 'avi': '🎥', 'mkv': '🎥',\n"
"        'zip': '📦', 'rar': '📦',\n"
"        'js': '📜', 'html': '📜', 'css': '📜', 'py': '📜',\n"
"      };\n"
"      \n"
"      return iconMap[ext] || '📄';\n"
"    }\n"
"\n"
"    function getFileType(name, type) {\n"
"      if (type === 'dir') return 'Folder';\n"
"      \n"
"      const ext = name.split('.').pop().toLowerCase();\n"
"      const typeMap = {\n"
"        'pdf': 'PDF',\n"
"        'doc': 'Word', 'docx': 'Word',\n"
"        'txt': 'Text',\n"
"        'xls': 'Excel', 'xlsx': 'Excel',\n"
"        'jpg': 'Image', 'jpeg': 'Image', 'png': 'Image',\n"
"        'mp3': 'Audio', 'wav': 'Audio',\n"
"        'mp4': 'Video', 'avi': 'Video',\n"
"        'zip': 'Archive', 'rar': 'Archive',\n"
"        'js': 'JavaScript', 'html': 'HTML', 'css': 'CSS',\n"
"      };\n"
"      \n"
"      return typeMap[ext] || 'File';\n"
"    }\n"
"\n"
"    function showStatus(message) {\n"
"      const statusEl = document.getElementById('statusMessage');\n"
"      statusEl.innerHTML = `<div class=\"status-message\">${message}</div>`;\n"
"      setTimeout(() => {\n"
"        statusEl.innerHTML = '';\n"
"      }, 3000);\n"
"    }\n"
"\n"
"    // API functions\n"
"    async function apiCall(endpoint, options = {}) {\n"
"      try {\n"
"        const response = await fetch(endpoint, options);\n"
"        if (response.ok) {\n"
"          return await response.json();\n"
"        }\n"
"      } catch (error) {\n"
"        // Hata mesajlarını göstermiyoruz\n"
"      }\n"
"      return null;\n"
"    }\n"
"\n"
"    async function listDirectory(path) {\n"
"      const data = await apiCall(`/api/list?path=${encodeURIComponent(path)}`);\n"
"      if (data) {\n"
"        currentEntries = data;\n"
"        updateFileListing();\n"
"        updateStats();\n"
"        updateBreadcrumb(path);\n"
"        currentPath = path;\n"
"      }\n"
"    }\n"
"\n"
"    async function createDirectory(path) {\n"
"      const result = await apiCall(`/api/mkdir?path=${encodeURIComponent(path)}`, { method: 'POST' });\n"
"      if (result !== null) {\n"
"        await listDirectory(currentPath);\n"
"        showStatus('Folder created successfully');\n"
"        return true;\n"
"      }\n"
"      return false;\n"
"    }\n"
"\n"
"    async function deleteItem(path) {\n"
"      if (!confirm('Are you sure you want to delete this item?')) return false;\n"
"      \n"
"      const result = await apiCall(`/api/delete?path=${encodeURIComponent(path)}`, { method: 'POST' });\n"
"      if (result !== null) {\n"
"        await listDirectory(currentPath);\n"
"        showStatus('Item deleted successfully');\n"
"        return true;\n"
"      }\n"
"      return false;\n"
"    }\n"
"\n"
"    async function uploadFile(file, destination) {\n"
"      try {\n"
"        const response = await fetch(`/api/upload?path=${encodeURIComponent(destination)}`, {\n"
"          method: 'PUT',\n"
"          body: file\n"
"        });\n"
"        return response.ok;\n"
"      } catch (error) {\n"
"        return false;\n"
"      }\n"
"    }\n"
"\n"
"    async function createFile(path, content = '') {\n"
"      try {\n"
"        const response = await fetch(`/api/upload?path=${encodeURIComponent(path)}`, {\n"
"          method: 'PUT',\n"
"          body: content\n"
"        });\n"
"        return response.ok;\n"
"      } catch (error) {\n"
"        return false;\n"
"      }\n"
"    }\n"
"\n"
"    async function viewFile(path) {\n"
"      try {\n"
"        const response = await fetch(`/api/download?path=${encodeURIComponent(path)}`);\n"
"        if (response.ok) {\n"
"          const contentType = response.headers.get('content-type') || '';\n"
"          \n"
"          if (contentType.includes('image')) {\n"
"            const blob = await response.blob();\n"
"            const url = URL.createObjectURL(blob);\n"
"            return `<img src=\"${url}\" alt=\"${path}\">`;\n"
"          } else if (contentType.includes('text') || contentType.includes('application/json')) {\n"
"            return await response.text();\n"
"          } else {\n"
"            return 'Binary file - Download to view content';\n"
"          }\n"
"        }\n"
"      } catch (error) {\n"
"        // Hata mesajlarını göstermiyoruz\n"
"      }\n"
"      return 'Unable to load file content';\n"
"    }\n"
"\n"
"    // UI update functions\n"
"    function updateFileListing() {\n"
"      const fileRows = document.getElementById('fileRows');\n"
"      fileRows.innerHTML = '';\n"
"\n"
"      // Add parent directory link if not at root\n"
"      if (currentPath !== '/') {\n"
"        const parentPath = currentPath.split('/').slice(0, -1).join('/') || '/';\n"
"        const row = document.createElement('div');\n"
"        row.className = 'file-row';\n"
"        row.innerHTML = `\n"
"          <div class=\"file-name\">\n"
"            <div class=\"file-icon\">📁</div>\n"
"            <a href=\"#\" data-path=\"${parentPath}\">..</a>\n"
"          </div>\n"
"          <div class=\"file-size\">-</div>\n"
"          <div class=\"file-type\">Parent Directory</div>\n"
"          <div class=\"file-actions\"></div>\n"
"        `;\n"
"        fileRows.appendChild(row);\n"
"      }\n"
"\n"
"      // Sort entries: directories first, then files\n"
"      const sortedEntries = [...currentEntries].sort((a, b) => {\n"
"        if (a.type === b.type) {\n"
"          return a.name.localeCompare(b.name);\n"
"        }\n"
"        return a.type === 'dir' ? -1 : 1;\n"
"      });\n"
"\n"
"      // Add file entries\n"
"      sortedEntries.forEach(entry => {\n"
"        const row = document.createElement('div');\n"
"        row.className = 'file-row';\n"
"        \n"
"        const icon = getFileIcon(entry.type, entry.name);\n"
"        const typeName = getFileType(entry.name, entry.type);\n"
"        const size = entry.type === 'dir' ? '-' : formatBytes(entry.size || 0);\n"
"        \n"
"        let nameContent;\n"
"        if (entry.type === 'dir') {\n"
"          nameContent = `<a href=\"#\" data-path=\"${entry.path}\">${entry.name}</a>`;\n"
"        } else {\n"
"          nameContent = `<a href=\"#\" class=\"view-file\" data-path=\"${entry.path}\">${entry.name}</a>`;\n"
"        }\n"
"        \n"
"        row.innerHTML = `\n"
"          <div class=\"file-name\">\n"
"            <div class=\"file-icon\">${icon}</div>\n"
"            ${nameContent}\n"
"          </div>\n"
"          <div class=\"file-size\">${size}</div>\n"
"          <div class=\"file-type\">${typeName}</div>\n"
"          <div class=\"file-actions\">\n"
"            <button class=\"action-btn download-btn\" title=\"Download\" ${entry.type === 'dir' ? 'disabled' : ''} data-path=\"${entry.path}\">\n"
"              <span class=\"nav-icon\">⬇️</span>\n"
"            </button>\n"
"            <button class=\"action-btn rename-btn\" title=\"Rename\" data-path=\"${entry.path}\" data-name=\"${entry.name}\">\n"
"              <span class=\"nav-icon\">✏️</span>\n"
"            </button>\n"
"            <button class=\"action-btn delete-btn\" title=\"Delete\" data-path=\"${entry.path}\">\n"
"              <span class=\"nav-icon\">🗑️</span>\n"
"            </button>\n"
"          </div>\n"
"        `;\n"
"        \n"
"        fileRows.appendChild(row);\n"
"      });\n"
"\n"
"      // Add event listeners\n"
"      setupEventListeners();\n"
"    }\n"
"\n"
"    function updateStats() {\n"
"      const folders = currentEntries.filter(e => e.type === 'dir').length;\n"
"      const files = currentEntries.filter(e => e.type !== 'dir').length;\n"
"      const totalSize = currentEntries\n"
"        .filter(e => e.type !== 'dir')\n"
"        .reduce((sum, e) => sum + (e.size || 0), 0);\n"
"\n"
"      document.getElementById('folderCount').textContent = folders;\n"
"      document.getElementById('fileCount').textContent = files;\n"
"      document.getElementById('totalSize').textContent = formatBytes(totalSize);\n"
"      document.getElementById('itemsCount').textContent = folders + files;\n"
"    }\n"
"\n"
"    function updateBreadcrumb(path) {\n"
"      const breadcrumb = document.getElementById('breadcrumb');\n"
"      const parts = path.split('/').filter(p => p);\n"
"      \n"
"      let breadcrumbHTML = '<a data-path=\"/\">Home</a>';\n"
"      let currentPath = '';\n"
"      \n"
"      parts.forEach(part => {\n"
"        currentPath += '/' + part;\n"
"        breadcrumbHTML += `<span class=\"breadcrumb-separator\">/</span><a data-path=\"${currentPath}\">${part}</a>`;\n"
"      });\n"
"      \n"
"      breadcrumb.innerHTML = breadcrumbHTML;\n"
"    }\n"
"\n"
"    // Event handlers\n"
"    function setupEventListeners() {\n"
"      // Directory navigation\n"
"      document.querySelectorAll('a[data-path]').forEach(link => {\n"
"        link.addEventListener('click', (e) => {\n"
"          e.preventDefault();\n"
"          const path = link.getAttribute('data-path');\n"
"          listDirectory(path);\n"
"        });\n"
"      });\n"
"\n"
"      // File actions\n"
"      document.querySelectorAll('.download-btn').forEach(btn => {\n"
"        btn.addEventListener('click', (e) => {\n"
"          e.stopPropagation();\n"
"          const path = btn.getAttribute('data-path');\n"
"          if (!btn.disabled) {\n"
"            window.open(`/api/download?path=${encodeURIComponent(path)}`, '_blank');\n"
"          }\n"
"        });\n"
"      });\n"
"\n"
"      document.querySelectorAll('.rename-btn').forEach(btn => {\n"
"        btn.addEventListener('click', (e) => {\n"
"          e.stopPropagation();\n"
"          const path = btn.getAttribute('data-path');\n"
"          const name = btn.getAttribute('data-name');\n"
"          openRenameModal(path, name);\n"
"        });\n"
"      });\n"
"\n"
"      document.querySelectorAll('.delete-btn').forEach(btn => {\n"
"        btn.addEventListener('click', (e) => {\n"
"          e.stopPropagation();\n"
"          const path = btn.getAttribute('data-path');\n"
"          deleteItem(path);\n"
"        });\n"
"      });\n"
"\n"
"      // File viewing\n"
"      document.querySelectorAll('.view-file').forEach(link => {\n"
"        link.addEventListener('click', (e) => {\n"
"          e.preventDefault();\n"
"          const path = link.getAttribute('data-path');\n"
"          openFileViewer(path);\n"
"        });\n"
"      });\n"
"\n"
"      // Sidebar navigation\n"
"      document.querySelectorAll('.nav-item[data-path]').forEach(item => {\n"
"        item.addEventListener('click', () => {\n"
"          const path = item.getAttribute('data-path');\n"
"          listDirectory(path);\n"
"          \n"
"          // Update active state\n"
"          document.querySelectorAll('.nav-item').forEach(nav => nav.classList.remove('active'));\n"
"          item.classList.add('active');\n"
"        });\n"
"      });\n"
"    }\n"
"\n"
"    // Modal functions\n"
"    function openRenameModal(path, currentName) {\n"
"      itemToRename = path;\n"
"      document.getElementById('renameName').value = currentName;\n"
"      document.getElementById('renameModal').classList.add('active');\n"
"    }\n"
"\n"
"    async function openFileViewer(path) {\n"
"      document.getElementById('fileViewerTitle').textContent = `Viewing: ${path.split('/').pop()}`;\n"
"      document.getElementById('fileViewerContent').textContent = 'Loading...';\n"
"      document.getElementById('fileViewerModal').classList.add('active');\n"
"      \n"
"      const content = await viewFile(path);\n"
"      document.getElementById('fileViewerContent').innerHTML = content;\n"
"      \n"
"      itemToView = path;\n"
"    }\n"
"\n"
"    function closeAllModals() {\n"
"      document.querySelectorAll('.modal-overlay').forEach(modal => {\n"
"        modal.classList.remove('active');\n"
"      });\n"
"    }\n"
"\n"
"    // Initialize the app\n"
"    function init() {\n"
"      // Refresh button\n"
"      document.getElementById('refreshBtn').addEventListener('click', () => {\n"
"        listDirectory(currentPath);\n"
"      });\n"
"\n"
"      // New Folder Modal\n"
"      document.getElementById('newFolderBtn').addEventListener('click', () => {\n"
"        document.getElementById('folderName').value = '';\n"
"        document.getElementById('newFolderModal').classList.add('active');\n"
"      });\n"
"\n"
"      document.getElementById('createFolderBtn').addEventListener('click', async () => {\n"
"        const folderName = document.getElementById('folderName').value.trim();\n"
"        if (!folderName) return;\n"
"        \n"
"        const newPath = currentPath.endsWith('/') \n"
"          ? currentPath + folderName \n"
"          : currentPath + '/' + folderName;\n"
"        \n"
"        const success = await createDirectory(newPath);\n"
"        if (success) {\n"
"          closeAllModals();\n"
"        }\n"
"      });\n"
"\n"
"      // New File Modal\n"
"      document.getElementById('newFileBtn').addEventListener('click', () => {\n"
"        document.getElementById('fileName').value = '';\n"
"        document.getElementById('fileContent').value = '';\n"
"        document.getElementById('newFileModal').classList.add('active');\n"
"      });\n"
"\n"
"      document.getElementById('createFileBtn').addEventListener('click', async () => {\n"
"        const fileName = document.getElementById('fileName').value.trim();\n"
"        if (!fileName) return;\n"
"        \n"
"        const fileContent = document.getElementById('fileContent').value;\n"
"        const newPath = currentPath.endsWith('/') \n"
"          ? currentPath + fileName \n"
"          : currentPath + '/' + fileName;\n"
"        \n"
"        const success = await createFile(newPath, fileContent);\n"
"        if (success) {\n"
"          await listDirectory(currentPath);\n"
"          showStatus('File created successfully');\n"
"          closeAllModals();\n"
"        }\n"
"      });\n"
"\n"
"      // Upload Modal\n"
"      document.getElementById('uploadBtn').addEventListener('click', () => {\n"
"        document.getElementById('fileUpload').value = '';\n"
"        document.getElementById('uploadProgress').innerHTML = '';\n"
"        document.getElementById('uploadModal').classList.add('active');\n"
"      });\n"
"\n"
"      document.getElementById('startUploadBtn').addEventListener('click', async () => {\n"
"        const fileInput = document.getElementById('fileUpload');\n"
"        const files = Array.from(fileInput.files);\n"
"        \n"
"        if (files.length === 0) return;\n"
"        \n"
"        const progressContainer = document.getElementById('uploadProgress');\n"
"        progressContainer.innerHTML = '';\n"
"        \n"
"        let uploadSuccess = true;\n"
"        \n"
"        for (const file of files) {\n"
"          const progressItem = document.createElement('div');\n"
"          progressItem.className = 'upload-item';\n"
"          progressItem.innerHTML = `\n"
"            <div><strong>${file.name}</strong></div>\n"
"            <div>Uploading...</div>\n"
"          `;\n"
"          progressContainer.appendChild(progressItem);\n"
"          \n"
"          const destination = currentPath.endsWith('/') \n"
"            ? currentPath + file.name \n"
"            : currentPath + '/' + file.name;\n"
"          \n"
"          const success = await uploadFile(file, destination);\n"
"          if (success) {\n"
"            progressItem.innerHTML = `\n"
"              <div><strong>${file.name}</strong></div>\n"
"              <div style=\"color: green;\">✓ Uploaded successfully</div>\n"
"            `;\n"
"          } else {\n"
"            progressItem.innerHTML = `\n"
"              <div><strong>${file.name}</strong></div>\n"
"              <div>Upload failed</div>\n"
"            `;\n"
"            uploadSuccess = false;\n"
"          }\n"
"        }\n"
"        \n"
"        if (uploadSuccess) {\n"
"          setTimeout(() => {\n"
"            closeAllModals();\n"
"            listDirectory(currentPath);\n"
"            showStatus('Files uploaded successfully');\n"
"          }, 1000);\n"
"        }\n"
"      });\n"
"\n"
"      // Rename Modal\n"
"      document.getElementById('confirmRenameBtn').addEventListener('click', async () => {\n"
"        const newName = document.getElementById('renameName').value.trim();\n"
"        if (!newName) return;\n"
"        \n"
"        if (!itemToRename) return;\n"
"        \n"
"        const oldPath = itemToRename;\n"
"        const oldDir = oldPath.substring(0, oldPath.lastIndexOf('/'));\n"
"        const newPath = oldDir === '' ? '/' + newName : oldDir + '/' + newName;\n"
"        \n"
"        // For rename, we'll use upload to overwrite or create new and delete old\n"
"        try {\n"
"          // Download old file content if it's a file\n"
"          const isDir = currentEntries.find(e => e.path === oldPath)?.type === 'dir';\n"
"          \n"
"          if (isDir) {\n"
"            // For directories, we can't easily rename with current API\n"
"            showStatus('Renaming directories not supported in this version');\n"
"          } else {\n"
"            // For files: download, upload with new name, delete old\n"
"            const response = await fetch(`/api/download?path=${encodeURIComponent(oldPath)}`);\n"
"            if (response.ok) {\n"
"              const content = await response.blob();\n"
"              const uploadSuccess = await uploadFile(content, newPath);\n"
"              if (uploadSuccess) {\n"
"                await deleteItem(oldPath);\n"
"                showStatus('File renamed successfully');\n"
"              }\n"
"            }\n"
"          }\n"
"          \n"
"          closeAllModals();\n"
"          await listDirectory(currentPath);\n"
"        } catch (error) {\n"
"          // Hata mesajlarını göstermiyoruz\n"
"        }\n"
"      });\n"
"\n"
"      // File Viewer Modal\n"
"      document.getElementById('downloadViewerBtn').addEventListener('click', () => {\n"
"        if (itemToView) {\n"
"          window.open(`/api/download?path=${encodeURIComponent(itemToView)}`, '_blank');\n"
"        }\n"
"      });\n"
"\n"
"      // Close modal handlers\n"
"      document.getElementById('closeFolderModal').addEventListener('click', closeAllModals);\n"
"      document.getElementById('closeFileModal').addEventListener('click', closeAllModals);\n"
"      document.getElementById('closeUploadModal').addEventListener('click', closeAllModals);\n"
"      document.getElementById('closeRenameModal').addEventListener('click', closeAllModals);\n"
"      document.getElementById('closeFileViewerModal').addEventListener('click', closeAllModals);\n"
"      document.getElementById('closeViewerBtn').addEventListener('click', closeAllModals);\n"
"\n"
"      document.getElementById('cancelFolderBtn').addEventListener('click', closeAllModals);\n"
"      document.getElementById('cancelFileBtn').addEventListener('click', closeAllModals);\n"
"      document.getElementById('cancelUploadBtn').addEventListener('click', closeAllModals);\n"
"      document.getElementById('cancelRenameBtn').addEventListener('click', closeAllModals);\n"
"\n"
"      // Close modal when clicking outside\n"
"      document.addEventListener('click', (e) => {\n"
"        if (e.target.classList.contains('modal-overlay')) {\n"
"          closeAllModals();\n"
"        }\n"
"      });\n"
"\n"
"      // Search functionality\n"
"      document.getElementById('searchInput').addEventListener('input', (e) => {\n"
"        const searchTerm = e.target.value.toLowerCase();\n"
"        \n"
"        if (searchTerm === '') {\n"
"          updateFileListing();\n"
"          return;\n"
"        }\n"
"        \n"
"        const filteredEntries = currentEntries.filter(entry => \n"
"          entry.name.toLowerCase().includes(searchTerm)\n"
"        );\n"
"        \n"
"        const fileRows = document.getElementById('fileRows');\n"
"        fileRows.innerHTML = '';\n"
"\n"
"        filteredEntries.forEach(entry => {\n"
"          const row = document.createElement('div');\n"
"          row.className = 'file-row';\n"
"          \n"
"          const icon = getFileIcon(entry.type, entry.name);\n"
"          const typeName = getFileType(entry.name, entry.type);\n"
"          const size = entry.type === 'dir' ? '-' : formatBytes(entry.size || 0);\n"
"          \n"
"          let nameContent;\n"
"          if (entry.type === 'dir') {\n"
"            nameContent = `<a href=\"#\" data-path=\"${entry.path}\">${entry.name}</a>`;\n"
"          } else {\n"
"            nameContent = `<a href=\"#\" class=\"view-file\" data-path=\"${entry.path}\">${entry.name}</a>`;\n"
"          }\n"
"          \n"
"          row.innerHTML = `\n"
"            <div class=\"file-name\">\n"
"              <div class=\"file-icon\">${icon}</div>\n"
"              ${nameContent}\n"
"            </div>\n"
"            <div class=\"file-size\">${size}</div>\n"
"            <div class=\"file-type\">${typeName}</div>\n"
"            <div class=\"file-actions\">\n"
"              <button class=\"action-btn download-btn\" title=\"Download\" ${entry.type === 'dir' ? 'disabled' : ''} data-path=\"${entry.path}\">\n"
"                <span class=\"nav-icon\">⬇️</span>\n"
"              </button>\n"
"              <button class=\"action-btn rename-btn\" title=\"Rename\" data-path=\"${entry.path}\" data-name=\"${entry.name}\">\n"
"                <span class=\"nav-icon\">✏️</span>\n"
"              </button>\n"
"              <button class=\"action-btn delete-btn\" title=\"Delete\" data-path=\"${entry.path}\">\n"
"                <span class=\"nav-icon\">🗑️</span>\n"
"              </button>\n"
"            </div>\n"
"          `;\n"
"          \n"
"          fileRows.appendChild(row);\n"
"        });\n"
"\n"
"        setupEventListeners();\n"
"      });\n"
"\n"
"      // Load initial directory\n"
"      listDirectory('/');\n"
"    }\n"
"\n"
"    // Start the application\n"
"    document.addEventListener('DOMContentLoaded', init);\n"
"  </script>\n"
"</body>\n"
"</html>\n";

/* ---------- HTTP request parsing helpers ---------- */

struct http_req {
    char method[16];
    char uri[PATH_MAX];
    char proto[16];
    char headers[BUFSIZE];
    char *body;
    size_t body_len;
};

/* parse incoming request buffer (single-chunk parse, simple) */
static int parse_request(int conn, struct http_req *req, char *buf, ssize_t rlen) {
    if (rlen <= 0) return -1;
    buf[rlen] = '\0';
    char *line_end = strstr(buf, "\r\n");
    if (!line_end) return -1;
    *line_end = '\0';
    if (sscanf(buf, "%15s %1023s %15s", req->method, req->uri, req->proto) != 3) return -1;
    char *p = line_end + 2;
    char *hdrend = strstr(p, "\r\n\r\n");
    if (!hdrend) {
        req->headers[0] = '\0';
        req->body = NULL; req->body_len = 0;
        return 0;
    }
    size_t hdrlen = hdrend - p;
    if (hdrlen >= sizeof(req->headers)) hdrlen = sizeof(req->headers) - 1;
    memcpy(req->headers, p, hdrlen);
    req->headers[hdrlen] = '\0';

    req->body = NULL; req->body_len = 0;
    char *cl = my_strcasestr(req->headers, "Content-Length:");
    if (cl) {
        char *num = cl + strlen("Content-Length:");
        while (*num && isspace((unsigned char)*num)) num++;
        int content_len = atoi(num);
        char *bodystart = hdrend + 4;
        ssize_t have = rlen - (bodystart - buf);
        if (content_len > 0) {
            req->body = malloc(content_len + 1);
            if (!req->body) return -1;
            if (have > 0) {
                size_t tocopy = (have < content_len) ? have : content_len;
                memcpy(req->body, bodystart, tocopy);
                size_t got = tocopy;
                while ((int)got < content_len) {
                    ssize_t nr = recv(conn, req->body + got, content_len - got, 0);
                    if (nr <= 0) break;
                    got += nr;
                }
                req->body_len = (size_t)content_len < got ? content_len : got;
            } else {
                size_t got = 0;
                while ((int)got < content_len) {
                    ssize_t nr = recv(conn, req->body + got, content_len - got, 0);
                    if (nr <= 0) break;
                    got += nr;
                }
                req->body_len = got;
            }
            req->body[req->body_len] = '\0';
        }
    }
    return 0;
}

/* header_get: find header name and return pointer to its value (within headers) */
static char *header_get(const char *headers, const char *name) {
    if (!headers || !name) return NULL;
    char *p = my_strcasestr(headers, name);
    if (!p) return NULL;
    char *colon = strchr(p, ':');
    if (!colon) return NULL;
    char *v = colon + 1;
    while (*v && isspace((unsigned char)*v)) v++;
    return v;
}

/* Check Basic Authorization header value */
static int check_basic_auth_header(const char *value) {
    if (!g_auth_enabled) return 1;
    if (!value) return 0;
    /* value is the header value (starting at "Basic ...") or may contain "Authorization: Basic ..." - handle both */
    const char *v = value;
    /* if it begins with "Authorization:", skip */
    if (strncasecmp(v, "Authorization:", 14) == 0) {
        v += 14;
        while (*v && isspace((unsigned char)*v)) v++;
    }
    if (strncasecmp(v, "Basic ", 6) != 0) return 0;
    v += 6;
    char dec[256];
    b64dec_simple(v, dec, sizeof(dec));
    char *sep = strchr(dec, ':');
    if (!sep) return 0;
    *sep = '\0';
    char *user = dec;
    char *pass = sep + 1;
    if (strcmp(user, g_user) == 0 && strcmp(pass, g_pass) == 0) return 1;
    return 0;
}

/* ---------- API handlers ---------- */

/* /api/list?path=... -> JSON array */
static void api_list(int conn, const char *reqpath) {
    char fs[PATH_MAX];
    join_path(fs, sizeof(fs), g_root, reqpath);
    DIR *d = opendir(fs);
    if (!d) {
        const char *empty = "[]";
        send_headers(conn, 200, "OK", "application/json; charset=utf-8", strlen(empty), NULL);
        send_all(conn, empty, strlen(empty));
        return;
    }
    struct dirent *e;
    char out[BUFSIZE];
    size_t pos = 0;
    pos += snprintf(out + pos, sizeof(out) - pos, "[");
    int first = 1;
    while ((e = readdir(d)) != NULL) {
        if (strcmp(e->d_name, ".") == 0 || strcmp(e->d_name, "..") == 0) continue;
        char childfs[PATH_MAX];
        snprintf(childfs, sizeof(childfs), "%s/%s", fs, e->d_name);
        struct stat st;
        if (stat(childfs, &st) != 0) continue;
        const char *type = S_ISDIR(st.st_mode) ? "dir" : "file";
        long long size = S_ISDIR(st.st_mode) ? 0 : (long long)st.st_size;
        /* sanitize name */
        char jsafe[PATH_MAX]; size_t j = 0;
        for (size_t k = 0; k < strlen(e->d_name) && j + 1 < sizeof(jsafe); ++k) {
            char c = e->d_name[k];
            if (c == '"' || c == '\\') { jsafe[j++] = '\\'; jsafe[j++] = c; }
            else jsafe[j++] = c;
        }
        jsafe[j] = '\0';
        char clientpath[PATH_MAX];
        if (strcmp(reqpath, "/") == 0) snprintf(clientpath, sizeof(clientpath), "/%s", e->d_name);
        else snprintf(clientpath, sizeof(clientpath), "%s/%s", reqpath, e->d_name);
        if (!first) pos += snprintf(out + pos, sizeof(out) - pos, ",");
        pos += snprintf(out + pos, sizeof(out) - pos,
                        "{\"name\":\"%s\",\"path\":\"%s\",\"type\":\"%s\",\"size\":%lld}",
                        jsafe, clientpath, type, size);
        first = 0;
        if (pos > sizeof(out) - 512) break;
    }
    closedir(d);
    pos += snprintf(out + pos, sizeof(out) - pos, "]");
    send_headers(conn, 200, "OK", "application/json; charset=utf-8", pos, NULL);
    send_all(conn, out, pos);
}

/* /api/download?path=... */
static void api_download(int conn, const char *reqpath) {
    char fs[PATH_MAX];
    join_path(fs, sizeof(fs), g_root, reqpath);
    struct stat st;
    if (stat(fs, &st) != 0 || S_ISDIR(st.st_mode)) {
        const char *nf = "Not found";
        send_headers(conn, 404, "Not Found", "text/plain; charset=utf-8", strlen(nf), NULL);
        send_all(conn, nf, strlen(nf));
        return;
    }
    int fd = open(fs, O_RDONLY);
    if (fd < 0) {
        const char *err = "Error";
        send_headers(conn, 500, "Error", "text/plain; charset=utf-8", strlen(err), NULL);
        send_all(conn, err, strlen(err));
        return;
    }
    off_t fsz = st.st_size;
    const char *ctype = "application/octet-stream";
    const char *ext = strrchr(fs, '.');
    if (ext) {
        if (!strcasecmp(ext, ".html") || !strcasecmp(ext, ".htm")) ctype = "text/html";
        else if (!strcasecmp(ext, ".txt")) ctype = "text/plain";
        else if (!strcasecmp(ext, ".json")) ctype = "application/json";
        else if (!strcasecmp(ext, ".jpg") || !strcasecmp(ext, ".jpeg")) ctype = "image/jpeg";
        else if (!strcasecmp(ext, ".png")) ctype = "image/png";
    }
    send_headers(conn, 200, "OK", ctype, (size_t)fsz, NULL);
    char buf[BUFSIZE];
    ssize_t n;
    while ((n = read(fd, buf, sizeof(buf))) > 0) {
        if (send_all(conn, buf, n) <= 0) break;
    }
    close(fd);
}

/* PUT /api/upload?path=... -> req->body */
static void api_upload(int conn, const char *reqpath, struct http_req *req) {
    if (!req || req->body_len == 0) {
        const char *nb = "No body";
        send_headers(conn, 400, "Bad Request", "text/plain", strlen(nb), NULL);
        send_all(conn, nb, strlen(nb));
        return;
    }
    char fs[PATH_MAX];
    join_path(fs, sizeof(fs), g_root, reqpath);
    /* ensure parent dirs */
    char tmp[PATH_MAX]; strncpy(tmp, fs, sizeof(tmp)-1);
    char *slash = strrchr(tmp, '/');
    if (slash) {
        *slash = '\0';
        char accum[PATH_MAX] = {0};
        char *tok, *save;
        tok = strtok_r((tmp[0]=='/'? tmp+1: tmp), "/", &save);
        if (tmp[0]=='/') strcpy(accum, "/");
        while (tok) {
            strcat(accum, tok);
            strcat(accum, "/");
            mkdir(accum, 0755);
            tok = strtok_r(NULL, "/", &save);
        }
    }
    int fd = open(fs, O_CREAT | O_TRUNC | O_WRONLY, 0644);
    if (fd < 0) {
        const char *err = "Failed";
        send_headers(conn, 500, "Internal", "text/plain", strlen(err), NULL);
        send_all(conn, err, strlen(err));
        return;
    }
    ssize_t w = write(fd, req->body, req->body_len);
    close(fd);
    if ((size_t)w != req->body_len) {
        const char *err = "Write failed";
        send_headers(conn, 500, "Internal", "text/plain", strlen(err), NULL);
        send_all(conn, err, strlen(err));
        return;
    }
    const char *ok = "Created";
    send_headers(conn, 201, "Created", "text/plain", strlen(ok), NULL);
    send_all(conn, ok, strlen(ok));
}

/* POST /api/mkdir?path=... */
static void api_mkdir(int conn, const char *reqpath) {
    char fs[PATH_MAX];
    join_path(fs, sizeof(fs), g_root, reqpath);
    /* recursive mkdir */
    char tmp[PATH_MAX]; strncpy(tmp, fs, sizeof(tmp)-1);
    char *p = tmp;
    if (*p == '/') p++;
    char accum[PATH_MAX] = {0};
    if (fs[0] == '/') strcpy(accum, "/");
    char *tok, *save;
    tok = strtok_r(p, "/", &save);
    while (tok) {
        strcat(accum, tok);
        strcat(accum, "/");
        mkdir(accum, 0755);
        tok = strtok_r(NULL, "/", &save);
    }
    const char *ok = "Created";
    send_headers(conn, 201, "Created", "text/plain", strlen(ok), NULL);
    send_all(conn, ok, strlen(ok));
}

/* POST /api/delete?path=... */
static void api_delete(int conn, const char *reqpath) {
    char fs[PATH_MAX];
    join_path(fs, sizeof(fs), g_root, reqpath);
    struct stat st;
    if (lstat(fs, &st) != 0) {
        const char *nf = "Not found";
        send_headers(conn, 404, "Not Found", "text/plain", strlen(nf), NULL);
        send_all(conn, nf, strlen(nf));
        return;
    }
    int rc = 0;
    if (S_ISDIR(st.st_mode)) rc = rmdir(fs); else rc = unlink(fs);
    if (rc == 0) send_headers(conn, 204, "No Content", NULL, 0, NULL);
    else { const char *err = "Error"; send_headers(conn, 500, "Internal", "text/plain", strlen(err), NULL); send_all(conn, err, strlen(err)); }
}

/* Serve UI */
static void serve_index(int conn) {
    size_t len = strlen(INDEX_HTML);
    send_headers(conn, 200, "OK", "text/html; charset=utf-8", len, NULL);
    send_all(conn, INDEX_HTML, len);
}

/* ---------- Connection worker ---------- */

static void *conn_thread(void *arg) {
    int conn = (intptr_t)arg;
    char buf[BUFSIZE + 1];
    ssize_t r = recv(conn, buf, BUFSIZE, 0);
    if (r <= 0) { close(conn); return NULL; }
    struct http_req req;
    memset(&req, 0, sizeof(req));
    if (parse_request(conn, &req, buf, r) != 0) { close(conn); return NULL; }

    char *authhdr = header_get(req.headers, "Authorization");
    if (!check_basic_auth_header(authhdr)) {
        const char *hdr = "WWW-Authenticate: Basic realm=\"WebFS\"\r\n";
        send_headers(conn, 401, "Unauthorized", "text/plain", 13, hdr);
        send_all(conn, "Unauthorized\n", 13);
        if (req.body) free(req.body);
        close(conn);
        return NULL;
    }

    /* Route requests */
    if (strcasecmp(req.method, "GET") == 0 && (strcmp(req.uri, "/") == 0 || strncmp(req.uri, "/?path=", 6) == 0)) {
        serve_index(conn);
    } else if (strcasecmp(req.method, "GET") == 0 && strncmp(req.uri, "/api/list", 9) == 0) {
        char *q = strchr(req.uri, '?');
        if (!q) { api_list(conn, "/"); }
        else {
            char tmp[PATH_MAX]; strncpy(tmp, q+1, sizeof(tmp)-1);
            char *p = strstr(tmp, "path=");
            if (!p) api_list(conn, "/");
            else {
                p += 5; char *amp = strchr(p, '&'); if (amp) *amp = '\0';
                char dec[PATH_MAX]; url_decode(dec, p);
                api_list(conn, dec);
            }
        }
    } else if (strcasecmp(req.method, "GET") == 0 && strncmp(req.uri, "/api/download", 13) == 0) {
        char *q = strchr(req.uri, '?'); if (!q) { send_headers(conn, 400, "Bad Request", "text/plain", 11, NULL); send_all(conn, "Bad Request", 11); }
        else {
            char tmp[PATH_MAX]; strncpy(tmp, q+1, sizeof(tmp)-1);
            char *p = strstr(tmp, "path="); if (!p) { send_headers(conn, 400, "Bad Request", "text/plain", 11, NULL); send_all(conn, "Bad Request", 11); }
            else { p += 5; char *amp = strchr(p, '&'); if (amp) *amp = '\0'; char dec[PATH_MAX]; url_decode(dec, p); api_download(conn, dec); }
        }
    } else if (strcasecmp(req.method, "PUT") == 0 && strncmp(req.uri, "/api/upload", 11) == 0) {
        char *q = strchr(req.uri, '?'); if (!q) { send_headers(conn, 400, "Bad Request", "text/plain", 11, NULL); send_all(conn, "Bad Request", 11); }
        else {
            char tmp[PATH_MAX]; strncpy(tmp, q+1, sizeof(tmp)-1);
            char *p = strstr(tmp, "path="); if (!p) { send_headers(conn, 400, "Bad Request", "text/plain", 11, NULL); send_all(conn, "Bad Request", 11); }
            else { p += 5; char *amp = strchr(p, '&'); if (amp) *amp = '\0'; char dec[PATH_MAX]; url_decode(dec, p); api_upload(conn, dec, &req); }
        }
    } else if (strcasecmp(req.method, "POST") == 0 && strncmp(req.uri, "/api/mkdir", 10) == 0) {
        char *q = strchr(req.uri, '?'); if (!q) { send_headers(conn, 400, "Bad Request", "text/plain", 11, NULL); send_all(conn, "Bad Request", 11); }
        else {
            char tmp[PATH_MAX]; strncpy(tmp, q+1, sizeof(tmp)-1);
            char *p = strstr(tmp, "path="); if (!p) { send_headers(conn, 400, "Bad Request", "text/plain", 11, NULL); send_all(conn, "Bad Request", 11); }
            else { p += 5; char *amp = strchr(p, '&'); if (amp) *amp = '\0'; char dec[PATH_MAX]; url_decode(dec, p); api_mkdir(conn, dec); }
        }
    } else if (strcasecmp(req.method, "POST") == 0 && strncmp(req.uri, "/api/delete", 11) == 0) {
        char *q = strchr(req.uri, '?'); if (!q) { send_headers(conn, 400, "Bad Request", "text/plain", 11, NULL); send_all(conn, "Bad Request", 11); }
        else {
            char tmp[PATH_MAX]; strncpy(tmp, q+1, sizeof(tmp)-1);
            char *p = strstr(tmp, "path="); if (!p) { send_headers(conn, 400, "Bad Request", "text/plain", 11, NULL); send_all(conn, "Bad Request", 11); }
            else { p += 5; char *amp = strchr(p, '&'); if (amp) *amp = '\0'; char dec[PATH_MAX]; url_decode(dec, p); api_delete(conn, dec); }
        }
    } else {
        const char *nf = "Not Found";
        send_headers(conn, 404, "Not Found", "text/plain", strlen(nf), NULL);
        send_all(conn, nf, strlen(nf));
    }

    if (req.body) free(req.body);
    close(conn);
    return NULL;
}

/* ---------- Server loop ---------- */

static void run_server(void) {
    int listenfd = socket(AF_INET, SOCK_STREAM, 0);
    if (listenfd < 0) fatal("socket: %s\n", strerror(errno));
    int optval = 1;
    setsockopt(listenfd, SOL_SOCKET, SO_REUSEADDR, &optval, sizeof(optval));
    struct sockaddr_in srv = {0};
    srv.sin_family = AF_INET;
    srv.sin_addr.s_addr = htonl(INADDR_ANY);
    srv.sin_port = htons(g_port);
    if (bind(listenfd, (struct sockaddr*)&srv, sizeof(srv)) < 0) fatal("bind: %s\n", strerror(errno));
    if (listen(listenfd, BACKLOG) < 0) fatal("listen: %s\n", strerror(errno));
    fprintf(stderr, "WebFS listening on 0.0.0.0:%d, root=%s\n", g_port, g_root);
    while (1) {
        struct sockaddr_in cli; socklen_t clen = sizeof(cli);
        int conn = accept(listenfd, (struct sockaddr*)&cli, &clen);
        if (conn < 0) continue;
        pthread_t th;
        pthread_create(&th, NULL, conn_thread, (void*)(intptr_t)conn);
        pthread_detach(th);
    }
}

/* ---------- CLI ---------- */

static void usage(const char *prog) {
    fprintf(stderr, "WebFS - minimal HTTP file manager for jailbroken iOS\n");
    fprintf(stderr, "Usage: %s [-p port] [-r root] [-u user -P pass]\n", prog);
}

int main(int argc, char **argv) {
    int opt;
    while ((opt = getopt(argc, argv, "p:r:u:P:h")) != -1) {
        switch (opt) {
            case 'p': g_port = atoi(optarg); break;
            case 'r': strncpy(g_root, optarg, sizeof(g_root)-1); break;
            case 'u': strncpy(g_user, optarg, sizeof(g_user)-1); break;
            case 'P': strncpy(g_pass, optarg, sizeof(g_pass)-1); break;
            case 'h':
            default: usage(argv[0]); return 0;
        }
    }
    if (g_user[0] && g_pass[0]) g_auth_enabled = 1;
    if (!is_jailbroken()) fprintf(stderr, "Warning: device does not appear jailbroken. Server may lack privileges.\n");
    if (g_root[0] == 0) strcpy(g_root, "/");
    run_server();
    return 0;

}
/*
* SUPPORTED ARCH arm64
* TESTED ON PALERA1N ROOTFUL JAILBREAK
* PALERA1N WEBSITE: https://palera.in
* More Tools: https://github.com/iosmenq
* Contact Me: magmalya.project@gmail.com
*** END ***

