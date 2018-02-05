/**************************************************************************/
/*                                                                        */
/*  The Why3 Verification Platform   /   The Why3 Development Team        */
/*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University        */
/*                                                                        */
/*  This software is distributed under the terms of the GNU Lesser        */
/*  General Public License version 2.1, with the special exception        */
/*  on linking described in file LICENSE.                                 */
/*                                                                        */
/**************************************************************************/

#ifndef ARRAYLIST_H
#define ARRAYLIST_H

#include <stdbool.h>

// A simple list implementation based on a resizable array. The list has a
// field "key" which allows to lookup certain members by this key.

typedef struct {
  int* key;     // the key data, as an array
  void** data;  // the actual list data, as an array
  int len;      // the number of elements in the list
  int capacity; // the capacity of the arrays key and data
} t_list, *plist;
// The idea is that each element in the list is a tuple (key, data), but it is
// simpler to have two separate arrays for that

// return a list of initial capacity <capacity>
plist init_list(int capacity);

// add a new element <elt> to the list <l>, with <key>. The array will
// automatically grow if more space is needed.
void list_append(plist l, int key, void* elt);

// return true if the list is empty, false otherwise
bool list_is_empty(plist l);

// return the number of elements in the list
int list_length(plist l);

// remove the element in the list whose key is equal to <key>. If no such data
// exists, do nothing.
void list_remove(plist l, int key);

// Return the data whose key is equal to <key>. Return NULL if no such data
// exists.
void* list_lookup(plist l, int key);

// free storage associated with the list. The list must be empty when freeing
// it.
void free_list(plist l);

#endif
