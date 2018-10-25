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
#include <stdarg.h>
#include "logging.h"
#include "options.h"

FILE* logfile;

void init_logging() {
  if (logging) {
   logfile = fopen("why3server.log", "w");
  }
}

void log_msg(char* fmt, ...) {
  if (logging) {
    va_list va;
    va_start(va, fmt);
    vfprintf(logfile, fmt, va);
    fprintf(logfile, "\n");
    fflush (logfile);
    va_end(va);
  }
}

void logging_shutdown(char* s) {
  if (logging) {
    log_msg("%s",s);
    fclose(logfile);
  }
  exit(1);
}
