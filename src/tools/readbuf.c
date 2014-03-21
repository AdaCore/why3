#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include "readbuf.h"

void resize_readbuf(preadbuf b, int newcapacity);

preadbuf init_readbuf(int capacity) {
  assert (capacity = 1);
  preadbuf buf;
  buf = (preadbuf) malloc(sizeof(t_readbuf));
  buf->capacity = capacity;
  buf->len = 0;
  buf->data = (char*) malloc(sizeof(char) * capacity);
  return buf;
}

void resize_readbuf(preadbuf b, int newcapacity) {
  b->data = (char*) realloc(b->data, sizeof(char) * newcapacity);
  b->capacity = newcapacity;
}

char* prepare_read(preadbuf b, int size) {
  if (b->len + size > b->capacity) {
     resize_readbuf(b, (b->capacity + size) * 2);
  }
  return b->data + b->len;
}

void have_read(preadbuf b, int size) {
  assert(b->capacity >= b->len + size);
  b->len += size;
}

void have_taken(preadbuf b, int size) {
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
