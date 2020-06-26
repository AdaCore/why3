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
#include <string.h>
#include <stdio.h>
#include "writebuf.h"

pwritebuf init_writebuf(int capacity) {
   pwritebuf buf = (pwritebuf) malloc(sizeof(t_writebuf));
   buf->data = NULL;
   buf->len = 0;
   buf->pointer = 0;
   buf->is_writing = false;
   buf->writequeue = init_queue(capacity);
   return buf;
}

char* prepare_write(pwritebuf b, int* size) {
   assert (can_write(b));
   assert (has_write_data(b));
   b->is_writing = true;
   *size = b->len - b->pointer;
   return (b->data + b->pointer);
}

void have_written(pwritebuf b, int size) {
   assert (b->is_writing);
   assert (b->pointer + size <= b->len);
   b->is_writing = false;
   if (b->pointer + size < b->len) {
      b->pointer += size;
   } else {
      free(b->data);
      b->pointer = 0;
      if (!queue_is_empty(b->writequeue)) {
         b->data = queue_pop(b->writequeue);
         b->len = strlen(b->data);
      } else {
         b->data = NULL;
         b->len = 0;
      }
   }
}

bool can_write(pwritebuf b) {
   return (!b->is_writing);
}

bool has_write_data(pwritebuf b) {
   return (b->data != NULL);
}

void push_write_data(pwritebuf b, char* data) {
   if (has_write_data (b)) {
      queue_push(b->writequeue, (void*) data);
   } else {
      b->data = data;
      b->pointer = 0;
      b->len = strlen(data);
   }
}

//delete all data associated with the buffer
void free_writebuf(pwritebuf b) {
   free(b->data);
   while (!queue_is_empty(b->writequeue)) {
      free(queue_pop(b->writequeue));
   }
   free_queue(b->writequeue);
   free(b);
}
