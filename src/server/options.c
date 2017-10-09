/********************************************************************/
/*                                                                  */
/*  The Why3 Verification Platform   /   The Why3 Development Team  */
/*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  */
/*                                                                  */
/*  This software is distributed under the terms of the GNU Lesser  */
/*  General Public License version 2.1, with the special exception  */
/*  on linking described in file LICENSE.                           */
/*                                                                  */
/********************************************************************/

#include <getopt.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include "options.h"

int parallel = 1;
char* basename = NULL;
bool logging = false;
bool single_client = false;

void parse_options(int argc, char **argv) {
  static struct option long_options[] = {
    /* These options set a flag. */
    {"socket", required_argument, 0, 's'},
    {"logging", no_argument, 0, 'l'},
    {"single-client", no_argument, 0, 'i'},
    {0, 0, 0, 0}
  };
  while (1) {
     int option_index = 0;
     char c = 0;
     c = getopt_long (argc, argv, "j:s:",
                      long_options, &option_index);
     /* Detect the end of the options. */
     if (c == -1) break;

     switch (c) {
       case 0:
         /* The case where a long option has been detected for --socket should
            be handled like the short option, as a NULL value was given for the
            corresponding flag in long_options. */
         exit (1);

       case 'i':
         single_client = true;
         break;

       case 'j':
         errno = 0;
         parallel = strtol(optarg, NULL, 10);
         if (errno == EINVAL) {
            printf("-j requires a number\n");
            exit(1);
         }
         if (parallel <= 0 ) {
            printf("-j requires a positive number\n");
            exit(1);
         }
         break;

       case 'l':
         logging = true;
         break;

       case 's':
         basename = optarg;
         break;

       case '?':
         /* getopt_long already printed an error message. */
         exit (1);

       default:
         exit (1);
     }
  }
  if (optind < argc) {
    printf("extra arguments, stopping [opt_index=%d,argc=%d]\n",optind,argc);
    exit(1);
  }
  if (basename == NULL) {
    printf("need to specify a socket name using --socket\n");
    exit(1);
  }
}
