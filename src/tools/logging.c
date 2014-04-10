#include <stdio.h>
#include <stdlib.h>
#include "logging.h"

FILE* logfile;

void init_logging() {
   logfile = fopen("why3server.log", "w");
}

void log_msg(char* s) {
   fprintf (logfile, "%s\n", s);
}

void logging_shutdown(char* s) {
   log_msg(s);
   fclose(logfile);
   exit(1);
}
