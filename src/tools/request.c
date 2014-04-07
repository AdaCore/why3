#include "request.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

//count the semicolons in <buf>, up to <len>
int count_semicolons(char* buf, int len);

//in <buf>, starting from index <begin> and up to index <len-1>, search for a
//semicolon. If a semicolon is found at index i, copy the substring from
//<begin> to <i-1>, that is, excluding the semicolon, into <result>, which
//will be allocated to contain that much space + a null terminator.
//If no semicolon is found, the part of <buf> starting from <begin> up to len
//is copied instead.
int copy_up_to_semicolon(char* buf, int begin, int len, char** result);

int count_semicolons(char* buf, int len) {
  int cnt = 0;
  int i = 0;
  for (i = 0; i < len; i++) {
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
  int numargs;
  int i = 0;
  int pos = 0;
  prequest req;
  char* tmp;

  numargs = count_semicolons(str_req, len) - 3;
  if ( numargs < 0) {
    return NULL;
  }
  req = (prequest) malloc(sizeof(request));
  req->key = key;
  req->numargs = numargs;
  pos = copy_up_to_semicolon(str_req, pos, len, &(req->id));
  pos = copy_up_to_semicolon(str_req, pos, len, &tmp);
  if (tmp) {
    req->timeout = atoi(tmp);
    free(tmp);
  }
  pos = copy_up_to_semicolon(str_req, pos, len, &tmp);
  if (tmp) {
    req->memlimit = atoi(tmp);
    free(tmp);
  }
  pos = copy_up_to_semicolon(str_req, pos, len, &(req->cmd));
  req->args = (char**)malloc(sizeof(char*) * (numargs));
  for (i = 0; i < numargs; i++) {
    pos = copy_up_to_semicolon(str_req, pos, len, &(req->args[i]));
  }
  return req;
}

void print_request(prequest r) {
  int i;
  if (r) {
    printf("%s %d %d %s", r->id, r->timeout, r->memlimit, r->cmd);
    for (i = 0; i < r->numargs; i++) {
       printf(" %s", r->args[i]);
    }
  } else {
    printf("<null>");
  }
}

void free_request(prequest r) {
  int i;
  free(r->cmd);
  for (i = 0;i < r->numargs; i++) {
    free(r->args[i]);
  }
  free(r->args);
  free(r);
}
