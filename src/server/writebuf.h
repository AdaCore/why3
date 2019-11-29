/********************************************************************/
/*                                                                  */
/*  The Why3 Verification Platform   /   The Why3 Development Team  */
/*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  */
/*                                                                  */
/*  This software is distributed under the terms of the GNU Lesser  */
/*  General Public License version 2.1, with the special exception  */
/*  on linking described in file LICENSE.                           */
/*                                                                  */
/********************************************************************/

#ifndef WRITEBUF_H
#define WRITEBUF_H

#include <stdbool.h>
#include "queue.h"

// Implement a write buffer, which is intended to be used for write/WriteFile
// operations. The buffer is essentially a queue of things to write, plus the
// "current write". Before doing a write, call <prepare_write>, which returns
// the writebuffer with the number of bytes to write. After the write,
// register the number of bytes written using <have_written>.
// In between a pair of calls <prepare_write>/<have_written>. the function
// <can_write> returns false.

typedef struct {
  char* data;
  int len;
  int pointer;
  bool is_writing;
  pqueue writequeue;
} t_writebuf, *pwritebuf;

pwritebuf init_writebuf(int capacity);

//return a pointer to the memory region which needs to be written next
//size will be initialized after the call to the number of bytes to write
//ideally
char* prepare_write(pwritebuf b, int* size);

//notify the buffer that <size> bytes have been written
void have_written(pwritebuf b, int size);

//return false if we are currently waiting for a write already, equivalently,
//if since the last call to <prepare_write>, <have_written> has not been
//called.
bool can_write(pwritebuf b);

// return true if the buffer has data to write
bool has_write_data(pwritebuf b);

// append new data to the write buffer
void push_write_data(pwritebuf b, char* data);

//delete all data associated with the buffer
void free_writebuf(pwritebuf b);
#endif
