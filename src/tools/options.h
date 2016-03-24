#ifndef OPTIONS_H
#define OPTIONS_H

#include <stdbool.h>

extern int parallel;
extern char* basename;
extern bool logging;

//parse command line options and set the variables <basename> and <parallel>
void parse_options(int argc, char **argv);

#endif
