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

extern int parallel;
extern char* basename;
extern bool logging;
extern bool single_client;

//parse command line options and set the variables <basename> and <parallel>
void parse_options(int argc, char **argv);

#endif
