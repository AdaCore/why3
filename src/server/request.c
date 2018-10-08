/********************************************************************/
/*                                                                  */
/*  The Why3 Verification Platform   /   The Why3 Development Team  */
/*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  */
/*                                                                  */
/*  This software is distributed under the terms of the GNU Lesser  */
/*  General Public License version 2.1, with the special exception  */
/*  on linking described in file LICENSE.                           */
/*                                                                  */
/********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "request.h"
#include "options.h"
#include "logging.h"

// Global pointers are initialized with NULL by C semantics
pqueue queue;

//count the semicolons in <buf>, up to <len>
int count_semicolons(char* buf, int len);

//in <buf>, starting from index <begin> and up to index <len-1>, search for a
//semicolon. If a semicolon is found at index i, copy the substring from
//<begin> to <i-1>, that is, excluding the semicolon, into <result>, which
//will be allocated to contain that much space + a null terminator.
//If no semicolon is found, the part of <buf> starting from <begin> up to <len-1>
//is copied instead, and a null terminator added.
int copy_up_to_semicolon(char* buf, int begin, int len, char** result);

int count_semicolons(char* buf, int len) {
  int cnt = 0;
  for (int i = 0; i < len; i++) {
    if (buf[i] == ';') {
      cnt++;
    }
  }
  return cnt;
}

int copy_up_to_semicolon(char* buf, int begin, int len, char** result) {
  int i;
  for (i = begin; i < len; i++) {
    if (buf[i] == ';') {
      break;
    }
  }
  (*result) = (char*) malloc(sizeof(char) * (i - begin + 1));
  memcpy((*result), buf + begin, i - begin);
  (*result)[i - begin] = '\0';
  if (i == len) {
    return 0;
  } else {
    return i + 1;
  }
}

prequest parse_request(char* str_req, int len, int key) {
  int numargs, semic, parallel_arg;
  int pos = 0;
  prequest req;
  char* tmp;
  bool runstdin = false;

  log_msg("received query %.*s",len,str_req);

  semic = count_semicolons(str_req, len);
  if (semic == 0) {
    return NULL;
  }
  if (semic == 1) {
    //  might be a 'parallel' or a 'interrupt' command
    pos = copy_up_to_semicolon (str_req, pos, len, &tmp);
    if (strncmp(tmp, "parallel", pos) == 0) {
      free(tmp);
      pos = copy_up_to_semicolon (str_req, pos, len, &tmp);
      parallel_arg = atoi(tmp);
      if (parallel_arg >= 1) {
        parallel = parallel_arg;
      }
    }
    else if (strncmp(tmp, "interrupt", pos) == 0) {
      free(tmp);
      req = (prequest) malloc(sizeof(request));
      req->key = key;
      req->req_type = REQ_INTERRUPT;
      pos = copy_up_to_semicolon(str_req, pos, len, &(req->id));
      return req;
    }
    free(tmp);
    return NULL;
  }

  numargs = semic - 4;
  if (numargs < 0) {
    return NULL;
  }
  pos = copy_up_to_semicolon(str_req, pos, len, &tmp);
  if (strncmp(tmp, "run", pos) != 0) {
    if (strncmp(tmp, "runstdin", pos) == 0) {
      runstdin = true;
    } else {
      free(tmp);
      return NULL;
    }
  }
  free(tmp);
  req = (prequest) malloc(sizeof(request));
  req->key = key;
  req->req_type = REQ_RUN;
  req->numargs = numargs;
  req->usestdin = runstdin;
  pos = copy_up_to_semicolon(str_req, pos, len, &(req->id));
  pos = copy_up_to_semicolon(str_req, pos, len, &tmp);
  req->timeout = atoi(tmp);
  free(tmp);
  pos = copy_up_to_semicolon(str_req, pos, len, &tmp);
  req->memlimit = atoi(tmp);
  free(tmp);
  pos = copy_up_to_semicolon(str_req, pos, len, &(req->cmd));
  req->args = (char**)malloc(sizeof(char*) * (numargs));
  for (int i = 0; i < numargs; i++) {
    pos = copy_up_to_semicolon(str_req, pos, len, &(req->args[i]));
  }
  return req;
}

void print_request(prequest r) {
  if (r) {
    switch (r->req_type) {
    case REQ_RUN:
      printf("req_type=REQ_RUN, timeout=%d, memlimit=%d, cmd=%s", r->timeout, r->memlimit, r->cmd);
      for (int i = 0; i < r->numargs; i++) {
        printf(" %s", r->args[i]);
      }
      break;
    case REQ_INTERRUPT:
      printf("req_type=REQ_INTERRUPT, id=%s", r->id);
      break;
    default:
      printf("request.print_request: ill-formed request");
    }
  }
  else {
    printf("<null request>");
  }
}

void free_request(prequest r) {
  if (r) {
    switch (r->req_type) {
    case REQ_RUN:
      free(r->cmd);
      for (int i = 0;i < r->numargs; i++) {
        free(r->args[i]);
      }
      free(r->args);
      break;
    case REQ_INTERRUPT:
      free(r->id);
      break;
    default:
        log_msg("bad argument for request.free_request()");
    }
    free(r);
  }
}

void init_request_queue () {
  queue = init_queue(100);
}

void remove_from_queue(char *id) {
  // inefficient, but what else?
  pqueue tmp = init_queue(queue->capacity);
  while (!queue_is_empty(queue)) {
    prequest r = queue_pop(queue);
    if (strcmp(r->id,id)) queue_push(tmp, r);
  }
  while (!queue_is_empty(tmp)) {
    prequest r = queue_pop(tmp);
    queue_push(queue, r);
  }
  free_queue(tmp);
}
