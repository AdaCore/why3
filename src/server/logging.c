/********************************************************************/
/*                                                                  */
/*  The Why3 Verification Platform   /   The Why3 Development Team  */
/*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  */
/*                                                                  */
/*  This software is distributed under the terms of the GNU Lesser  */
/*  General Public License version 2.1, with the special exception  */
/*  on linking described in file LICENSE.                           */
/*                                                                  */
/********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include "logging.h"
#include "options.h"

FILE* logfile;

void init_logging() {
  if (logging) {
   logfile = fopen("why3server.log", "w");
  }
}

void log_msg(char* s) {
  if (logging) {
   fprintf (logfile, "%s\n", s);
   fflush (logfile);
  }
}

void log_msg_len(char* s, int len) {
  if (logging) {
   fprintf (logfile, "%.*s\n", len, s);
   fflush (logfile);
  }
}

void logging_shutdown(char* s) {
  if (logging) {
   log_msg(s);
   fclose(logfile);
  }
  exit(1);
}
