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

#ifndef QUEUE_H
#define QUEUE_H

#include <stdbool.h>

// This module implements a simple resizable queue

typedef struct {
  void** data;   // the array which contains the actual enqueued data
  unsigned int pointer;   // the pointer to the element which will be returned by the
                 // next pop
  unsigned int len;       // the number of elements in the queue
  unsigned int capacity;  // the capacity of the queue, more precisely of the <data>
                 // array
} t_queue, *pqueue;

// return an empty queue of initial capacity <capacity>
pqueue init_queue(unsigned int capacity);

// remove the first element of the queue and return it. Fails if the queue is
// not empty.
void* queue_pop(pqueue q);

// push a new element to the end of the queue. If the capacity of the queue is
// not sufficient, the underlying storage is automatically increased.
void queue_push(pqueue q, void* elt);

// if the queue is empty, return true, otherwise false
bool queue_is_empty(pqueue q);

// return the length of the queue
unsigned int queue_length(pqueue q);

// free the memory associated with the queue. The queue must be empty at this
// point.
void free_queue(pqueue q);

#endif
