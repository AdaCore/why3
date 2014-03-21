#include <getopt.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include "options.h"

int parallel = 1;
char* basename = NULL;

void parse_options(int argc, char **argv) {
  static struct option long_options[] = {
    /* These options set a flag. */
    {"socket", required_argument,       0, 's'},
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
         // the case where a long option has been detected
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

       case 's':
         basename = optarg;
         break;

       case '?':
         /* getopt_long already printed an error message. */
         break;

       default:
         exit (1);
     }
  }
  if (optind < argc) {
    printf("extra arguments, stopping\n");
    exit(1);
  }
  if (basename == NULL) {
    printf("need to specify a socket name using --socket\n");
    exit(1);
  }
}

