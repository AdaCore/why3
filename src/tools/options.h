#ifndef OPTIONS_H
#define OPTIONS_H

extern int parallel;
extern char* basename;

//parse command line options and set the variables <basename> and <parallel>
void parse_options(int argc, char **argv);

#endif
