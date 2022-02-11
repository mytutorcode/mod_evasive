/*
mod_evasive for Apache 2
Copyright (c) by Jonathan A. Zdziarski

LICENSE

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.

*/

#include <sys/types.h>
#include <unistd.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <string.h>
#include <stdlib.h>
#include <sys/types.h>
#include <time.h>
#include <syslog.h>
#include <errno.h>
#include <netdb.h>

#define PCRE2_CODE_UNIT_WIDTH 8
#include <pcre2.h>

#include "httpd.h"
#include "http_core.h"
#include "http_config.h"
#include "http_log.h"
#include "http_request.h"
#include "http_main.h"

module AP_MODULE_DECLARE_DATA evasive_module;

/* Apache version < 2.4 compat */
#if HTTP_VERSION(AP_SERVER_MAJORVERSION_NUMBER, AP_SERVER_MINORVERSION_NUMBER) < 2004
	/* r->useragent_ip is more accurate in this case in Apache 2.4 */
	#define useragent_ip connection->remote_ip
#endif /* Apache version < 2.4 compat */

#ifdef APLOG_USE_MODULE
  APLOG_USE_MODULE(evasive);
#endif

/* BEGIN DoS Evasive Maneuvers Definitions */

#define MAILER	"/bin/mail %s"
#define  LOG( A, ... ) { openlog("mod_evasive", LOG_PID, LOG_DAEMON); syslog( A, __VA_ARGS__ ); closelog(); }

#define DEFAULT_HASH_TBL_SIZE   3097ul  // Default hash table size
#define DEFAULT_PAGE_COUNT      2       // Default maximum page hit count per interval
#define DEFAULT_SITE_COUNT      50      // Default maximum site hit count per interval
#define DEFAULT_PAGE_INTERVAL   1       // Default 1 Second page interval
#define DEFAULT_SITE_INTERVAL   1       // Default 1 Second site interval
#define DEFAULT_BLOCKING_PERIOD 10      // Default for Detected IPs; blocked for 10 seconds
#define DEFAULT_LOG_DIR		"/tmp"        // Default temp directory
#define DEFAULT_HTTP_REPLY HTTP_TOO_MANY_REQUESTS //(429)  // HTTP_FORBIDDEN // Default HTTP Reply code (403)

/* END DoS Evasive Maneuvers Definitions */

/* BEGIN NTT (Named Timestamp Tree) Headers */

enum { ntt_num_primes = 28 };

/* ntt root tree */
struct ntt {
	long size;
	long items;
	struct ntt_node **tbl;
};

/* ntt node (entry in the ntt root tree) */
struct ntt_node {
	char *key;
	time_t timestamp;
	long count;
	struct ntt_node *next;
};

/* ntt cursor */
struct ntt_c {
	long iter_index;
	struct ntt_node *iter_next;
};

static struct ntt *ntt_create(unsigned long size);
static int ntt_destroy(struct ntt *ntt);
static struct ntt_node	*ntt_find(struct ntt *ntt, const char *key);
static struct ntt_node	*ntt_insert(struct ntt *ntt, const char *key, time_t timestamp);
static int ntt_delete(struct ntt *ntt, const char *key);
static long ntt_hashcode(struct ntt *ntt, const char *key);
static struct ntt_node *c_ntt_first(struct ntt *ntt, struct ntt_c *c);
static struct ntt_node *c_ntt_next(struct ntt *ntt, struct ntt_c *c);

/* END NTT (Named Timestamp Tree) Headers */


/* BEGIN DoS Evasive Maneuvers Globals */

static struct ntt *hit_list;	// Our dynamic hash table
static unsigned long hash_table_size = DEFAULT_HASH_TBL_SIZE;

struct pcre_node {
    pcre2_code *re;
    struct pcre_node *next;
};

typedef struct {
	int enabled;
  int silent_enabled;
  int ignore_querystring_enabled;
	char *context;
	struct pcre_node *uri_whitelist;
	int page_count;
	int page_interval;
	int site_count;
	int site_interval;
	int blocking_period;
	char *email_notify;
	char *log_dir;
	char *system_command;
	int http_reply;
	int report_socket;
	char *ip_from_header;
} evasive_config;

static const char *whitelist(cmd_parms *cmd, void *dconfig, const char *ip);
static int is_whitelisted(const char *ip, evasive_config *cfg);
static int is_uri_whitelisted(const char *uri, evasive_config *cfg);

/* END DoS Evasive Maneuvers Globals */
static void * create_hit_list()
{
	hit_list = ntt_create(hash_table_size);
	return 0;
}

static void * create_dir_conf(apr_pool_t *p, char *context)
{
	context = context ? context : "(undefined context)";
	/* Create a new hit list for this listener */
	evasive_config *cfg = apr_pcalloc(p, sizeof(evasive_config));
	if (cfg) {
		cfg->enabled = 1;
    cfg->silent_enabled = 0;
    cfg->ignore_querystring_enabled = 1;
		cfg->context = strdup(context);
		cfg->uri_whitelist = NULL;
		cfg->page_count = DEFAULT_PAGE_COUNT;
		cfg->page_interval = DEFAULT_PAGE_INTERVAL;
		cfg->site_count = DEFAULT_SITE_COUNT;
		cfg->site_interval = DEFAULT_SITE_INTERVAL;
		cfg->email_notify = NULL;
		cfg->log_dir = NULL;
		cfg->system_command = NULL;
		cfg->http_reply = DEFAULT_HTTP_REPLY;
		cfg->report_socket = -1;
		cfg->ip_from_header = NULL;
	}

	return cfg;
}

static const char *whitelist_uri(cmd_parms *cmd, void *dconfig, const char *uri_re)
{
    evasive_config *cfg = (evasive_config *) dconfig;
    struct pcre_node *node;

    node = (struct pcre_node *) malloc(sizeof(struct pcre_node));
    if (node == NULL) {
        return NULL;
    }

    int errornumber;
    PCRE2_SIZE erroroffset;

    PCRE2_SPTR pattern;
    pattern = (PCRE2_SPTR) uri_re;

    node->re = pcre2_compile(
            pattern,               /* the pattern */
            PCRE2_ZERO_TERMINATED, /* indicates pattern is zero-terminated */
            0,                     /* default options */
            &errornumber,          /* for error number */
            &erroroffset,          /* for error offset */
            NULL);                 /* use default compile context */

    /* Compilation failed: print the error message and exit. */

    if (node->re == NULL)
    {
        PCRE2_UCHAR buffer[256];
        pcre2_get_error_message(errornumber, buffer, sizeof(buffer));
        printf("PCRE2 compilation failed at offset %d: %s\n", (int)erroroffset,
                buffer);
        return NULL;
    }

    node->next = cfg->uri_whitelist;
    cfg->uri_whitelist = node;
    return NULL;
}

static int access_checker(request_rec *r)
{
	int ret = OK;
	const char *ip_string = r->useragent_ip;

	evasive_config *cfg = (evasive_config *) ap_get_module_config(r->per_dir_config, &evasive_module);

	if (cfg->ip_from_header) {
		const char *http_header_ip = apr_table_get(r->headers_in, cfg->ip_from_header);
		if (http_header_ip) {
			ip_string = http_header_ip;
		}
	}

	/* BEGIN DoS Evasive Maneuvers Code */
	if (cfg->enabled && r->prev == NULL && r->main == NULL && hit_list != NULL) {
		char hash_key[2048];
		struct ntt_node *n;
		time_t t = time(NULL);

		/* Check whitelist */
		if (is_whitelisted(ip_string, cfg)){
		  ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, r,"UserAgent: %s is whitelisted, ignored by mod_evasive.", ip_string); 
			return OK;
    }
		/* First see if the IP itself is on "hold" */
		n = ntt_find(hit_list, ip_string);

		if (n != NULL && t-n->timestamp<cfg->blocking_period) {
      ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, r,"UserAgent: %s is on hold => wait longer in blocked land.", ip_string); 
			/* If the IP is on "hold", make it wait longer in 403 land */
			ret = cfg->http_reply;
			n->timestamp = t;

		/* Not on hold, check hit stats */
		} else {
			int url_count  = 0;
			int site_count = 0;
			/* Check whitelisted uris */
				if (is_uri_whitelisted(r->uri, cfg))
					return OK;


			/* Has URI been hit too much? */
      if(cfg->ignore_querystring_enabled){
        const char *hostname;      
        hostname = r->parsed_uri.hostname? r->parsed_uri.hostname:r->server->server_hostname;
			  snprintf(hash_key, 2048, "%s_%s:%s%s", ip_string, hostname,r->parsed_uri.port_str,r->parsed_uri.path);
      }else{
        snprintf(hash_key, 2048, "%s_%s", ip_string, r->unparsed_uri);
      }
      ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, r,"Page URI hashKey: %s, originalUri: %s",hash_key,r->unparsed_uri); 

			n = ntt_find(hit_list, hash_key);
			if (n != NULL) {
				/* If URI is being hit too much, add to "hold" list and 403 */
        ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, r,"PageHitStats: hashKey:%s, interval %ld, count:%ld ",hash_key,(t-n->timestamp),n->count); 
				if (t-n->timestamp<cfg->page_interval && n->count>=cfg->page_count) {
          ap_log_rerror(APLOG_MARK, APLOG_ERR, 0, r,"PageHit Limit Exceeded: hashKey:%s, req_interval: %ld < cfg_page_interval:%d, count: %ld >= limit:%d ",hash_key,t-n->timestamp,cfg->page_interval,n->count,cfg->page_count); 
					ret = cfg->http_reply;
					ntt_insert(hit_list,  ip_string, t);
				} else {

					/* Reset our hit count list as necessary */
					if (t-n->timestamp>=cfg->page_interval) {
            ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, r,"Reset PageHit by cfg_page_interval: hashKey:%s",hash_key); 
						n->count=0;
						n->timestamp=t;
					}
				}
				/* don't update ts, as 20 requests each 3 sec apart
				 * becomes equivalent to 20 requests in 3 seconds */
				n->count++;
				url_count = n->count;
			} else {
        ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, r,"Insert new Page for monitoring PageHits: hashKey:%s",hash_key); 
				ntt_insert(hit_list, hash_key, t);
			}

			/* Has site been hit too much? */
			snprintf(hash_key, 2048, "%s_S", ip_string);
      ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, r,"Site hashKey: %s",hash_key); 
			n = ntt_find(hit_list, hash_key);
			if (n != NULL) {

				/* If site is being hit too much, add to "hold" list and 403 */
				if (t-n->timestamp<cfg->site_interval && n->count>=cfg->site_count) {
          ap_log_rerror(APLOG_MARK, APLOG_ERR, 0, r,"Site Limit Exceeded: hashKey:%s, req_interval: %ld < cfg_site_interval:%d, count:%ld >= cfg_site_count:%d",hash_key,t-n->timestamp,cfg->site_interval,n->count,cfg->site_count); 
					ret = cfg->http_reply;
					ntt_insert(hit_list, ip_string, t);
				} else {

					/* Reset our hit count list as necessary */
					if (t-n->timestamp>=cfg->site_interval) {
            ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, r,"Reset SiteHit by cfg_site_interval: hashKey:%s",hash_key); 
						n->count=0;
						n->timestamp=t;
					}
				}
				/* don't update ts, as 20 requests each 3 seconds apart
				 * is the same as 20 req in 3 seconds */
				n->count++;
				site_count = n->count;
			} else {
        ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, r,"Insert new Site for monitoring PageHits: hashKey:%s",hash_key); 
				ntt_insert(hit_list, hash_key, t);
			}

			if (cfg->report_socket) {
				char *msg;
				if (index(ip_string, '\'') == NULL && index(ip_string, '\\') == NULL) {
					if (asprintf(&msg, "{'url_count':%d,'site_count':%d,'ip':'%s'}", url_count, site_count, ip_string)) {
						if (send(cfg->report_socket, msg, strlen(msg), 0)<0) {
							ap_log_rerror(APLOG_MARK, APLOG_INFO, 0, r,"Could not report DOS usage errno=%d\n", errno);
						}
						free(msg);
					}
					else {
						ap_log_rerror(APLOG_MARK, APLOG_ERR, 0, r,"Could not generate JSON errno=%d\n", errno);
					}
				}
				else {
					ap_log_rerror(APLOG_MARK, APLOG_ERR, 0, r,"Unexpected characters in IP address");
				}
			}
		}

		/* Perform email notification and system functions */
		if (ret == cfg->http_reply) {
			char filename[1024];
			struct stat s;
			FILE *file;

			apr_table_setn(r->err_headers_out, "Cache-Control", "no-cache");

			snprintf(filename, sizeof(filename), "%s/dos-%s", cfg->log_dir != NULL ? cfg->log_dir : DEFAULT_LOG_DIR, ip_string);
			if (stat(filename, &s)) {
				file = fopen(filename, "w");
				if (file != NULL) {
					fprintf(file, "%d\n", getpid());
					fclose(file);

					LOG(LOG_ALERT, "Blacklisting address %s: possible DoS attack.", ip_string);
					if (cfg->email_notify != NULL) {
						snprintf(filename, sizeof(filename), MAILER, cfg->email_notify);
						file = popen(filename, "w");
						if (file != NULL) {
							fprintf(file, "To: %s\n", cfg->email_notify);
							fprintf(file, "Subject: HTTP BLACKLIST %s\n\n", ip_string);
							fprintf(file, "mod_evasive HTTP Blacklisted %s\n", ip_string);
							pclose(file);
						}
					}

					if (cfg->system_command != NULL) {
						snprintf(filename, sizeof(filename), cfg->system_command, ip_string);
						if (system(filename)!=0) {
							ap_log_rerror(APLOG_MARK, APLOG_ERR, 0, r,"Log command failed: '%s'", filename);
						}
					}

				} else {
					LOG(LOG_ALERT, "Couldn't open logfile %s: %s",filename, strerror(errno));
          ap_log_rerror(APLOG_MARK, APLOG_ERR, 0, r,"Couldn't open logfile %s: %s",filename, strerror(errno)); 
				}

			} /* if (temp file does not exist) */

		} /* if (ret == HTTP_FORBIDDEN) */

	} /* if (r->prev == NULL && r->main == NULL && hit_list != NULL) */

	/* END DoS Evasive Maneuvers Code */

	if (ret == cfg->http_reply
		&& (ap_satisfies(r) != SATISFY_ANY || !ap_some_auth_required(r))) {
			ap_log_rerror(APLOG_MARK, APLOG_ERR, 0, r,"Client: %s denied by server configuration: %s", ip_string,r->filename);
	}

  if(cfg->silent_enabled){
    ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, r,"Silent mode enabled by server configuration, possible DOS request from client:%s to page:%s will be ignored(not blocked).", ip_string, r->filename);
    ret = OK;
	}

	return ret;
}

static int is_whitelisted(const char *ip, evasive_config *cfg) {
	char hashkey[128];
	char octet[4][4];
	char *dip;
	char *oct;
	int i = 0;

	memset(octet, 0, 16);
	dip = strdup(ip);
	if (dip == NULL)
		return 0;

	oct = strtok(dip, ".");
	while(oct != NULL && i<4) {
		if (strlen(oct)<=3)
			strcpy(octet[i], oct);
		i++;
		oct = strtok(NULL, ".");
	}
	free(dip);

	/* Exact Match */
	snprintf(hashkey, sizeof(hashkey), "W_%s", ip);
	if (ntt_find(hit_list, hashkey)!=NULL)
		return 1;

	/* IPv4 Wildcards */
	snprintf(hashkey, sizeof(hashkey), "W_%s.%s.%s.*", octet[0], octet[1], octet[2]);
	if (ntt_find(hit_list, hashkey)!=NULL)
		return 1;

	snprintf(hashkey, sizeof(hashkey), "W_%s.%s.*.*", octet[0], octet[1]);
	if (ntt_find(hit_list, hashkey)!=NULL)
		return 1;

	snprintf(hashkey, sizeof(hashkey), "W_%s.*.*.*", octet[0]);
	if (ntt_find(hit_list, hashkey)!=NULL)
		return 1;

	/* No match */
	return 0;
}

int is_uri_whitelisted(const char *path, evasive_config *cfg) {

    int rc;
    pcre2_match_data *match_data;

    PCRE2_SPTR subject;
    size_t subject_length;

    subject = (PCRE2_SPTR) path;
    subject_length = strlen((char *)subject);

    struct pcre_node *node;
    node = cfg->uri_whitelist;

    while (node != NULL) {
        match_data = pcre2_match_data_create_from_pattern(node->re, NULL);

        rc = pcre2_match(
                node->re,             /* the compiled pattern */
                subject,              /* the subject string */
                subject_length,       /* the length of the subject */
                0,                    /* start at offset 0 in the subject */
                0,                    /* default options */
                match_data,           /* block for storing the result */
                NULL);                /* use default match context */

        pcre2_match_data_free(match_data);   /* Release memory used for the match */

        if (rc >= 0) {
            // match
            return 1;
        }

        node = node->next;
    }

    // no match
    return 0;
}

static apr_status_t destroy_config(void *dconfig) {
	evasive_config *cfg = (evasive_config *) dconfig;
	ntt_destroy(hit_list);
	if (!cfg) {
		return APR_SUCCESS;
	}

	if (cfg->report_socket != -1) {
		close(cfg->report_socket);
	}

	free(cfg->email_notify);
	free(cfg->log_dir);
	free(cfg->system_command);
	free(cfg);
	return APR_SUCCESS;
}

/* BEGIN NTT (Named Timestamp Tree) Functions */

static unsigned long ntt_prime_list[ntt_num_primes] =
{
	53ul,         97ul,         193ul,       389ul,       769ul,
	1543ul,       3079ul,       6151ul,      12289ul,     24593ul,
	49157ul,      98317ul,      196613ul,    393241ul,    786433ul,
	1572869ul,    3145739ul,    6291469ul,   12582917ul,  25165843ul,
	50331653ul,   100663319ul,  201326611ul, 402653189ul, 805306457ul,
	1610612741ul, 3221225473ul, 4294967291ul
};


/* Find the numeric position in the hash table based on key and modulus */

static long ntt_hashcode(struct ntt *ntt, const char *key) {
	unsigned long val = 0;
	for (; *key; ++key) val = 5 * val + *key;
	return(val % ntt->size);
}

/* Creates a single node in the tree */

static struct ntt_node *ntt_node_create(const char *key) {
	char *node_key;
	struct ntt_node* node;

	node = (struct ntt_node *) malloc(sizeof(struct ntt_node));
	if (node == NULL) {
		return NULL;
	}
	if ((node_key = strdup(key)) == NULL) {
		free(node);
		return NULL;
	}
	node->key = node_key;
	node->timestamp = time(NULL);
	node->next = NULL;
	return(node);
}

/* Tree initializer */

static struct ntt *ntt_create(unsigned long size) {
	long i = 0;
	struct ntt *ntt = (struct ntt *) malloc(sizeof(struct ntt));

	if (ntt == NULL)
		return NULL;
	while (ntt_prime_list[i] < size) { i++; }
	ntt->size  = ntt_prime_list[i];
	ntt->items = 0;
	ntt->tbl   = (struct ntt_node **) calloc(ntt->size, sizeof(struct ntt_node *));
	if (ntt->tbl == NULL) {
		free(ntt);
		return NULL;
	}
	return(ntt);
}

/* Find an object in the tree */

static struct ntt_node *ntt_find(struct ntt *ntt, const char *key) {
	long hash_code;
	struct ntt_node *node;

	if (ntt == NULL) return NULL;

	hash_code = ntt_hashcode(ntt, key);
	node = ntt->tbl[hash_code];

	while (node) {
		if (!strcmp(key, node->key)) {
			return(node);
		}
		node = node->next;
	}
	return((struct ntt_node *)NULL);
}

/* Insert a node into the tree */

static struct ntt_node *ntt_insert(struct ntt *ntt, const char *key, time_t timestamp) {
	long hash_code;
	struct ntt_node *parent;
	struct ntt_node *node;
	struct ntt_node *new_node = NULL;

	if (ntt == NULL) return NULL;

	hash_code = ntt_hashcode(ntt, key);
	parent = NULL;
	node = ntt->tbl[hash_code];

	while (node != NULL) {
		if (strcmp(key, node->key) == 0) {
			new_node = node;
			node = NULL;
		}

		if (new_node == NULL) {
			parent = node;
			node = node->next;
		}
	}

	if (new_node != NULL) {
		new_node->timestamp = timestamp;
		new_node->count = 0;
		return new_node;
	}

	/* Create a new node */
	new_node = ntt_node_create(key);
	new_node->timestamp = timestamp;
	new_node->timestamp = 0;

	ntt->items++;

	/* Insert */
	if (parent) {  /* Existing parent */
		parent->next = new_node;
		return new_node;  /* Return the locked node */
	}

	/* No existing parent; add directly to hash table */
	ntt->tbl[hash_code] = new_node;
	return new_node;
}

/* Tree destructor */

static int ntt_destroy(struct ntt *ntt) {
	struct ntt_node *node, *next;
	struct ntt_c c;

	if (ntt == NULL) return -1;

	node = c_ntt_first(ntt, &c);
	while(node != NULL) {
		next = c_ntt_next(ntt, &c);
		ntt_delete(ntt, node->key);
		node = next;
	}

	free(ntt->tbl);
	free(ntt);
	ntt = (struct ntt *) NULL;

	return 0;
}

/* Delete a single node in the tree */

static int ntt_delete(struct ntt *ntt, const char *key) {
	long hash_code;
	struct ntt_node *parent = NULL;
	struct ntt_node *node;
	struct ntt_node *del_node = NULL;

	if (ntt == NULL) return -1;

	hash_code = ntt_hashcode(ntt, key);
	node        = ntt->tbl[hash_code];

	while (node != NULL) {
		if (strcmp(key, node->key) == 0) {
			del_node = node;
			node = NULL;
		}

		if (del_node == NULL) {
			parent = node;
			node = node->next;
		}
	}

	if (del_node != NULL) {

		if (parent) {
			parent->next = del_node->next;
		} else {
			ntt->tbl[hash_code] = del_node->next;
		}

		free(del_node->key);
		free(del_node);
		ntt->items--;

		return 0;
	}

	return -5;
}

/* Point cursor to first item in tree */

static struct ntt_node *c_ntt_first(struct ntt *ntt, struct ntt_c *c) {

	c->iter_index = 0;
	c->iter_next = (struct ntt_node *)NULL;
	return(c_ntt_next(ntt, c));
}

/* Point cursor to next iteration in tree */

static struct ntt_node *c_ntt_next(struct ntt *ntt, struct ntt_c *c) {
	long index;
	struct ntt_node *node = c->iter_next;

	if (ntt == NULL) return NULL;

	if (node) {
		if (node != NULL) {
			c->iter_next = node->next;
			return (node);
		}
	}

	if (! node) {
		while (c->iter_index < ntt->size) {
			index = c->iter_index++;

			if (ntt->tbl[index]) {
				c->iter_next = ntt->tbl[index]->next;
				return(ntt->tbl[index]);
			}
		}
	}
	return((struct ntt_node *)NULL);
}

/* END NTT (Named Pointer Tree) Functions */


/* BEGIN Configuration Functions */
static const char *whitelist(cmd_parms *cmd, void *dconfig, const char *ip)
{
	char entry[128];
	// @TODO per-site whitelist
	snprintf(entry, sizeof(entry), "W_%s", ip);
	ntt_insert(hit_list, entry, time(NULL));
  ap_log_error(APLOG_MARK,APLOG_MODULE_INDEX,APLOG_INFO, 0,"Whitelist configuration: %s ",ip); 
	return NULL;
}

static const char *
get_hash_tbl_size(cmd_parms *cmd, void *dconfig, const char *value) {
	long n = strtol(value, NULL, 0);

	if (n<=0) {
		hash_table_size = DEFAULT_HASH_TBL_SIZE;
	} else  {
		hash_table_size = n;
	}
ap_log_error(APLOG_MARK,APLOG_MODULE_INDEX,APLOG_INFO, 0,"HashTable size configuration: %ld",hash_table_size); 
	return NULL;
}

static const char *
get_enabled(cmd_parms *cmd, void *dconfig, const char *value) {
    evasive_config *cfg = (evasive_config *) dconfig;    
    cfg->enabled = (!strcmp("off", value)  || !strcmp("false", value)) ? 0 : 1;
    ap_log_error(APLOG_MARK,APLOG_MODULE_INDEX,APLOG_INFO, 0,"Enabled configuration: %d",cfg->enabled); 
    return NULL;
}

static const char *
get_silent_enabled(cmd_parms *cmd, void *dconfig, const char *value) {
    evasive_config *cfg = (evasive_config *) dconfig;    
    cfg->silent_enabled = (!strcmp("off", value)  || !strcmp("false", value)) ? 0 : 1;
    ap_log_error(APLOG_MARK,APLOG_MODULE_INDEX,APLOG_INFO, 0,"SilentMode configuration: %d",cfg->silent_enabled); 
    return NULL;
}

static const char *
get_ignore_querystring_enabled(cmd_parms *cmd, void *dconfig, const char *value) {
    evasive_config *cfg = (evasive_config *) dconfig;    
    cfg->ignore_querystring_enabled = (!strcmp("off", value)  || !strcmp("false", value)) ? 0 : 1;
    ap_log_error(APLOG_MARK,APLOG_MODULE_INDEX,APLOG_INFO, 0,"IgnoreQueryString configuration: %d",cfg->ignore_querystring_enabled); 
    return NULL;
}

static const char *
get_page_count(cmd_parms *cmd, void *dconfig, const char *value) {
    evasive_config *cfg = (evasive_config *) dconfig;
    long n = strtol(value, NULL, 0);    
    if (n<=0) {
        cfg->page_count = DEFAULT_PAGE_COUNT;
    } else {
        cfg->page_count = n;
    }
    ap_log_error(APLOG_MARK,APLOG_MODULE_INDEX,APLOG_INFO, 0,"Page-count configuration: %d ",cfg->page_count); 
    return NULL;
}

static const char *
get_site_count(cmd_parms *cmd, void *dconfig, const char *value) {
    evasive_config *cfg = (evasive_config *) dconfig;
    long n = strtol(value, NULL, 0);
    if (n<=0) {
        cfg->site_count = DEFAULT_SITE_COUNT;
    } else {
        cfg->site_count = n;
    }
    ap_log_error(APLOG_MARK,APLOG_MODULE_INDEX,APLOG_INFO, 0,"Site-count configuration: %d ",cfg->site_count); 
    return NULL;
}

static const char *
get_page_interval(cmd_parms *cmd, void *dconfig, const char *value) {
    evasive_config *cfg = (evasive_config *) dconfig;
    long n = strtol(value, NULL, 0);
    if (n<=0) {
        cfg->page_interval = DEFAULT_PAGE_INTERVAL;
    } else {
        cfg->page_interval = n;
    }
    ap_log_error(APLOG_MARK,APLOG_MODULE_INDEX,APLOG_INFO, 0,"Page-interval configuration: %d ",cfg->page_interval); 
    return NULL;
}

static const char *
get_site_interval(cmd_parms *cmd, void *dconfig, const char *value) {
    evasive_config *cfg = (evasive_config *) dconfig;
    long n = strtol(value, NULL, 0);    
    if (n<=0) {
        cfg->site_interval = DEFAULT_SITE_INTERVAL;
    } else {
        cfg->site_interval = n;
    }
    ap_log_error(APLOG_MARK,APLOG_MODULE_INDEX,APLOG_INFO, 0,"Site-interval configuration: %d ",cfg->site_interval); 
    return NULL;
}

static const char *
get_blocking_period(cmd_parms *cmd, void *dconfig, const char *value) {
    evasive_config *cfg = (evasive_config *) dconfig;
    long n = strtol(value, NULL, 0);
    if (n<=0) {
        cfg->blocking_period = DEFAULT_BLOCKING_PERIOD;
    } else {
        cfg->blocking_period = n;
    }
    ap_log_error(APLOG_MARK,APLOG_MODULE_INDEX,APLOG_INFO, 0,"Blocking period configuration: %d ",cfg->blocking_period); 
    return NULL;
}

static const char *
get_log_dir(cmd_parms *cmd, void *dconfig, const char *value) {
    evasive_config *cfg = (evasive_config *) dconfig;
    if (value != NULL && value[0] != 0) {
        if (cfg->log_dir != NULL)
            free(cfg->log_dir);
        cfg->log_dir = strdup(value);
    }
    ap_log_error(APLOG_MARK,APLOG_MODULE_INDEX,APLOG_INFO, 0,"Log dir configuration: %s ",cfg->log_dir); 
    return NULL;
}

static const char *
get_email_notify(cmd_parms *cmd, void *dconfig, const char *value) {
    evasive_config *cfg = (evasive_config *) dconfig;
    if (value != NULL && value[0] != 0) {
        if (cfg->email_notify != NULL)
            free(cfg->email_notify);
        cfg->email_notify = strdup(value);
    }
    ap_log_error(APLOG_MARK,APLOG_MODULE_INDEX,APLOG_INFO, 0,"Email notify configuration: %s ",cfg->email_notify); 
    return NULL;
}

static const char *
get_system_command(cmd_parms *cmd, void *dconfig, const char *value) {
    evasive_config *cfg = (evasive_config *) dconfig;
    if (value != NULL && value[0] != 0) {
        if (cfg->system_command != NULL)
            free(cfg->system_command);
        cfg->system_command = strdup(value);
    }
    ap_log_error(APLOG_MARK,APLOG_MODULE_INDEX,APLOG_INFO, 0,"System command configuration: %s ",cfg->system_command ); 
    return NULL;
}

static const char *
get_http_reply(cmd_parms *cmd, void *dconfig, const char *value) {
    evasive_config *cfg = (evasive_config *) dconfig;
    long reply = strtol(value, NULL, 0);
    if (reply <= 0) {
        cfg->http_reply = DEFAULT_HTTP_REPLY;
    } else {
        cfg->http_reply = reply;
    }
    ap_log_error(APLOG_MARK,APLOG_MODULE_INDEX,APLOG_INFO, 0,"HttpReply configuration: %d ",cfg->http_reply); 
    return NULL;
}

static const char *
get_ip_from_header(cmd_parms *cmd, void *dconfig, const char *value) {
    evasive_config *cfg = (evasive_config *) dconfig;
    if (value != NULL && value[0] != 0) {
        if (cfg->ip_from_header != NULL)
            free(cfg->system_command);
        cfg->ip_from_header = strdup(value);
    }
    ap_log_error(APLOG_MARK,APLOG_MODULE_INDEX,APLOG_INFO, 0,"IP from header configuration: %s ",cfg->ip_from_header);
    return NULL;
}


static const char *
get_report_dest(cmd_parms *cmd, void *dconfig, const char *value) {
	evasive_config *cfg = (evasive_config *) dconfig;
	if (value != NULL && value[0] != 0) {
		if (cfg->report_socket != -1) {
			close(cfg->report_socket);
			cfg->report_socket = -1;
		}
		char *hostname = strdup(value);
		char *port     = hostname;
		strsep(&port, ":");

		struct addrinfo hints;
		struct addrinfo *result = NULL, *rp = NULL;

		memset(&hints, 0, sizeof(struct addrinfo));

		hints.ai_family = AF_UNSPEC;    /* Allow IPv4 or IPv6 */
		hints.ai_socktype = SOCK_DGRAM; /* Datagram socket */
		hints.ai_flags = AI_PASSIVE;    /* For wildcard IP address */
		hints.ai_protocol = 0;          /* Any protocol */
		hints.ai_canonname = NULL;
		hints.ai_addr = NULL;
		hints.ai_next = NULL;

		int rc = getaddrinfo(hostname, port, &hints, &result);
		if (rc != 0) {
			const char *err = gai_strerror(rc);
			ap_log_error(APLOG_MARK,APLOG_MODULE_INDEX,APLOG_ERR, 0,"Could not resolve host:port '%s': %s", value, err);
		}

		for (rp = result; rp != NULL; rp = rp->ai_next) {
			int sfd = socket(rp->ai_family, rp->ai_socktype | SOCK_NONBLOCK, rp->ai_protocol);
			if (sfd == -1) {
				ap_log_error(APLOG_MARK,APLOG_MODULE_INDEX,APLOG_DEBUG, 0,"Could not create socket errno=%d", errno);
				continue;
			}
			if (connect(sfd, rp->ai_addr, rp->ai_addrlen) == 0) {
				cfg->report_socket = sfd;
				break;
			}
			ap_log_error(APLOG_MARK,APLOG_MODULE_INDEX,APLOG_DEBUG, 0,"Could not connect errno=%d", errno);
			close(sfd);
		}

		if (cfg->report_socket == -1) {
			ap_log_error(APLOG_MARK,APLOG_MODULE_INDEX,APLOG_ERR, 0,"Could not connect to host:port '%s'", value);
		}
	}
	ap_log_error(APLOG_MARK,APLOG_MODULE_INDEX,APLOG_ERR, 0,"DOS report destination configuration: %s ",cfg->system_command );
	return NULL;
}


/* END Configuration Functions */

static const command_rec access_cmds[] =
{
    AP_INIT_TAKE1("DOSEnabled", get_enabled, NULL, ACCESS_CONF|RSRC_CONF,
    	"Toggle mod_evasive within global/virtualhost/directory. Default on."),

    AP_INIT_TAKE1("DOSSilent", get_silent_enabled, NULL, ACCESS_CONF|RSRC_CONF,
    	"Enables silent mode. Value on - when limits exceeded request is logged and processed, off - when limits exceeded configured HTTPStatus is thrown and request processing is blocked. Default off."),
    
    AP_INIT_TAKE1("DOSIgnoreQueryString", get_ignore_querystring_enabled, NULL, ACCESS_CONF|RSRC_CONF,
    	"Determines if query string in requested URI should be ignored. Value on - query string ignored, off - use full URI with query string. Default on."),

    AP_INIT_TAKE1("DOSHashTableSize", get_hash_tbl_size, NULL, RSRC_CONF,
    	"Set size of hash table."),

    AP_INIT_TAKE1("DOSPageCount", get_page_count, NULL, ACCESS_CONF|RSRC_CONF,
        "Set maximum page hit count per interval."),

    AP_INIT_TAKE1("DOSSiteCount", get_site_count, NULL, ACCESS_CONF|RSRC_CONF,
        "Set maximum site hit count per interval."),

    AP_INIT_TAKE1("DOSPageInterval", get_page_interval, NULL, ACCESS_CONF|RSRC_CONF,
		"Set page interval."),

    AP_INIT_TAKE1("DOSSiteInterval", get_site_interval, NULL, ACCESS_CONF|RSRC_CONF,
        "Set site interval."),

    AP_INIT_TAKE1("DOSBlockingPeriod", get_blocking_period, NULL, ACCESS_CONF|RSRC_CONF,
        "Set blocking period for detected DoS IPs."),

    AP_INIT_TAKE1("DOSEmailNotify", get_email_notify, NULL, ACCESS_CONF|RSRC_CONF,
        "Set email notification."),

    AP_INIT_TAKE1("DOSLogDir", get_log_dir, NULL, ACCESS_CONF|RSRC_CONF,
        "Set log dir."),

    AP_INIT_TAKE1("DOSSystemCommand", get_system_command, NULL, ACCESS_CONF|RSRC_CONF,
        "Set system command on DoS."),

    AP_INIT_ITERATE("DOSWhitelist", whitelist, NULL, RSRC_CONF,
        "IP-addresses wildcards to whitelist."),

    AP_INIT_ITERATE("DOSWhitelistUri", whitelist_uri, NULL, RSRC_CONF,
            "Files/paths regexes to whitelist"),

    AP_INIT_TAKE1("DOSHTTPStatus", get_http_reply, NULL, ACCESS_CONF|RSRC_CONF,
        "HTTP reply code."),

    AP_INIT_TAKE1("DOSReportDest", get_report_dest, NULL, ACCESS_CONF|RSRC_CONF,
        "Set system command on DoS."),

    AP_INIT_TAKE1("DOSIPFromHeader", get_ip_from_header, NULL, ACCESS_CONF|RSRC_CONF,
        "Take IP address from request header."),

    { NULL }
};

static void register_hooks(apr_pool_t *p) {
	create_hit_list();
	ap_hook_access_checker(access_checker, NULL, NULL, APR_HOOK_MIDDLE);
	apr_pool_cleanup_register(p, NULL, apr_pool_cleanup_null, destroy_config);
}

module AP_MODULE_DECLARE_DATA evasive_module =
{
	STANDARD20_MODULE_STUFF,
	create_dir_conf,
	NULL,
	NULL,
	NULL,
	access_cmds,
	register_hooks
};
