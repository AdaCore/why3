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
#include "arraylist.h"

#define INVALID_INDEX (-1)

int list_lookup_index(plist l, int key);
void list_resize(plist l);

plist init_list(int capacity) {
  plist result;
  result = (plist) malloc (sizeof(t_list));
  result->capacity = capacity;
  result->len = 0;
  result->key = (int*) malloc(sizeof(int) * capacity);
  result->data = (void**) malloc(sizeof(void*) * capacity);
  return result;
}

bool list_is_empty(plist l) {
  return (l->len == 0);
}

int list_lookup_index(plist l, int key) {
  for (int i = 0; i < l->len; i++) {
    if (l->key[i] == key) {
       return i;
    }
  }
  return INVALID_INDEX;
}

void* list_lookup(plist l, int key) {
  int i = list_lookup_index(l, key);
  if (i == INVALID_INDEX) {
    return NULL;
  } else {
    return l->data[i];
  }
}

void list_remove(plist l, int key) {
  int i = list_lookup_index(l, key);
  if (i != INVALID_INDEX) {
    assert (!list_is_empty(l));
    l->len--;
    l->key[i] = l->key[l->len];
    l->data[i] = l->data[l->len];
  }
}

void free_list(plist l) {
  assert (list_is_empty(l));
  free(l->data);
  free(l->key);
  free(l);
}

void list_resize(plist l) {
  int newcap = l->capacity * 2;
  l->capacity = newcap;
  l->key = (int*) realloc(l->key, sizeof(int) * newcap);
  l->data = (void**) realloc(l->data, sizeof(void*) * newcap);
}

void list_append(plist l, int key, void* elt) {
  if (l->len == l->capacity) {
     list_resize(l);
  }
  l->key[l->len] = key;
  l->data[l->len] = elt;
  l->len++;
}

int list_length(plist l) {
  return l->len;
}
