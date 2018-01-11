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

#ifndef REQUEST_H
#define REQUEST_H

#include <stdbool.h>

typedef struct {
  int key;
  char* id;
  int timeout;
  int memlimit;
  bool usestdin;
  char* cmd;   // the command to execute
  int numargs; // the length of the following array
  char** args; // the arguments of the process to run (not including the command)
} request, *prequest;

//given a buffer str_req of meaningful data up to <len>, parse the client data
//and create a prequest object. Return NULL if there is a parse error. The
//prequest object's <key> field is set to the value of argument <key>.
prequest parse_request(char* str_req, int len, int key);

//debug code
void print_request(prequest r);

//does *not* free the id of the request
void free_request(prequest r);

#endif
