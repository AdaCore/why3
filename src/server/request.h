#ifndef REQUEST_H
#define REQUEST_H

typedef struct {
  int key;
  char* id;
  int timeout;
  int memlimit;
  char* cmd;   // the command to execute
  int numargs; // the length of the following array
  char** args; // the arguments of the process to run (not including the command)
} request, *prequest;

//given a buffer str_req of meaningful data up to <len>, parse the client data
//and create a prequest object. Return NULL if there is a parse error. The
//prequest object's <key> field is set to the value of argument <key>.
prequest parse_request(char* str_req, int len, int key);

//debug code
void print_request(prequest r);

//does *not* free the id of the request
void free_request(prequest r);

#endif
