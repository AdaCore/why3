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

#ifndef OPTIONS_H
#define OPTIONS_H

#include <stdbool.h>

// how many processes are allowed to run in parallel
extern int parallel;
// the name of the socket (path)
extern char* socketname;
// enable or disable logging
extern bool logging;
// start in single client mode
extern bool single_client;

//parse command line options and set the variables above
void parse_options(int argc, char **argv);

#endif
