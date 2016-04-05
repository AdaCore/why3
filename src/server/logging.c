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
  }
}

void logging_shutdown(char* s) {
  if (logging) {
   log_msg(s);
   fclose(logfile);
  }
   exit(1);
}
