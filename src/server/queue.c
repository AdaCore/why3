/********************************************************************/
/*                                                                  */
/*  The Why3 Verification Platform   /   The Why3 Development Team  */
/*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  */
/*                                                                  */
/*  This software is distributed under the terms of the GNU Lesser  */
/*  General Public License version 2.1, with the special exception  */
/*  on linking described in file LICENSE.                           */
/*                                                                  */
/********************************************************************/

#include <assert.h>
#include <stdlib.h>
#include "queue.h"
#include "string.h"

void simple_push(pqueue q, void* elt);
void resize_queue(pqueue q);

pqueue init_queue(unsigned int capacity) {
  assert (capacity > 0);
  pqueue res = (pqueue) malloc(sizeof(t_queue));
  res->capacity = capacity;
  res->len = 0;
  res->pointer = 0;
  res->data = (void**) malloc(sizeof(void*) * capacity);
  return res;
}

void* queue_pop(pqueue q) {
  void* tmp;
  assert (q->len > 0);
  tmp = q->data[q->pointer];
  q->len--;
  q->pointer = (q->pointer + 1) % q->capacity;
  return tmp;
}

void simple_push(pqueue q, void* elt) {
  q->data[(q->pointer + q->len) % q->capacity] = elt;
  q->len++;
}

void resize_queue(pqueue q) {
  unsigned int old_cap, new_cap, old_p, new_p;
  old_cap = q->capacity;
  old_p = q->pointer;
  new_cap = 2 * old_cap;
  new_p = new_cap - old_cap + old_p;
  q->data = (void**) realloc(q->data, sizeof(void*) * new_cap);
  memcpy(q->data + new_p,
         q->data + old_p,
         sizeof(void*) * (old_cap - old_p));
  q->capacity = new_cap;
  q->pointer = new_p;
}

void queue_push(pqueue q, void* elt) {
  if (q->len == q->capacity) {
    resize_queue(q);
  }
  simple_push(q, elt);
}

bool queue_is_empty(pqueue q) {
  return (q->len == 0);
}

unsigned int queue_length(pqueue q) {
  return (q->len);
}

void free_queue(pqueue q) {
  assert(queue_is_empty (q));
  free(q->data);
  free(q);
}
