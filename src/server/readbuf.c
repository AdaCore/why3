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

#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include "readbuf.h"

void resize_readbuf(preadbuf b, size_t newcapacity);

preadbuf init_readbuf(size_t capacity) {
  assert (capacity > 0);
  preadbuf buf;
  buf = (preadbuf) malloc(sizeof(t_readbuf));
  buf->capacity = capacity;
  buf->len = 0;
  buf->data = (char*) malloc(sizeof(char) * capacity);
  return buf;
}

void resize_readbuf(preadbuf b, size_t newcapacity) {
  b->data = (char*) realloc(b->data, sizeof(char) * newcapacity);
  b->capacity = newcapacity;
}

char* prepare_read(preadbuf b, size_t size) {
  if (b->len + size > b->capacity) {
     resize_readbuf(b, (b->capacity + size) * 2);
  }
  return b->data + b->len;
}

void have_read(preadbuf b, size_t size) {
  assert(b->capacity >= b->len + size);
  b->len += size;
}

void have_taken(preadbuf b, size_t size) {
  assert (size <= b->len);
  memcpy(b->data, b->data+size, b->len - size);
  b->len -= size;
}

void clear_readbuf(preadbuf b) {
  b->len = 0;
}

void free_readbuf(preadbuf b) {
  free(b->data);
  free(b);
}
