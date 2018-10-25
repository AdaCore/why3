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

// This is the unix implementation of the VC server. It uses the poll
// mechanism to wait for events, plus the "self pipe trick" to handle
// terminating child processes.
//
// Contrary to the situation on windows, e.g. a read event means that the next
// call to read() will not block.

#ifndef _WIN32

#include <sys/types.h>
#include <unistd.h>
#include <stdio.h>
#include <errno.h>
#include <fcntl.h>
#include <libgen.h>
#include <poll.h>
#include <stddef.h>
#include <stdlib.h>
#include <signal.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <assert.h>
#include "request.h"
#include "arraylist.h"
#include "readbuf.h"
#include "writebuf.h"
#include "options.h"
#include "logging.h"
#include "proc.h"

#define READ_ONCE 1024

typedef struct {
  int       kind;
  int       fd;
  preadbuf  readbuf;
  pwritebuf writebuf;
} t_client, *pclient;

int server_sock = -1;

// the poll list is the list of file descriptors for which we monitor certain
// events.
struct pollfd* poll_list;
int poll_num = 0;
int poll_len = 0;

// global pointers are initialized with NULL by C semantics
plist clients;
char *current_dir;

static int cpipe[2];

void shutdown_with_msg(char* msg);

void shutdown_with_msg(char* msg) {
  if (server_sock != -1) {
    close(server_sock);
  }
  if (clients != NULL) {
     for (int i = 0; i < list_length(clients); i++) {
       close(((pclient) clients->data[i])->fd);
     }
  }
  logging_shutdown(msg);
}

char* get_cur_dir() {
  return getcwd(NULL, 0);
}

void add_to_poll_list(int sock, short events) {
  if (poll_num == poll_len) {
    poll_len *= 2;
    poll_list = (struct pollfd*) realloc(poll_list, sizeof(struct pollfd) * poll_len);
  }
  poll_list[poll_num].fd = sock;
  poll_list[poll_num].events = events;
  poll_list[poll_num].revents = 0;
  poll_num++;
}

struct pollfd* poll_list_lookup(int fd) {
  for (int i = 0; i < poll_num; i++) {
    if (poll_list[i].fd == fd) {
      return poll_list+i;
    }
  }
  return NULL;
}

void poll_list_clean() {
  int i = 0;
  while (i < poll_num) {
    if (poll_list[i].fd == -1) {
      poll_list[i] = poll_list[poll_num - 1];
      --poll_num;
    } else ++i;
  }
}

void poll_list_remove(int fd) {
  for (int i = 0; i < poll_num; ++i) {
    if (poll_list[i].fd == fd) {
      poll_list[i].fd = -1;
      poll_list[i].revents = 0;
      break;
    }
  }
}

int open_temp_file(char* dir, char** outfile) {
  char* template;
  size_t len;
  len = strlen(dir);
  template = (char*) malloc(sizeof(char) * (len + 12));
  strcpy(template, dir);
  strcat(template, "/why3");
  strcat(template, "XXXXXX");
  (*outfile) = template;
  return mkstemp(template);
}

void server_accept_client() {
  struct sockaddr_un remote;
  pclient client;
  int fd;
  socklen_t len;
  len = sizeof(struct sockaddr_un);
  fd = accept(server_sock, (struct sockaddr*) &remote, &len);
  if (fd == -1) {
    shutdown_with_msg("error accepting a client");
  }
  client = (pclient) malloc(sizeof(t_client));
  client->fd = fd;
  client->readbuf = init_readbuf(READ_ONCE);
  client->writebuf = init_writebuf(parallel);
  list_append(clients, fd, (void*)client);
  add_to_poll_list(fd, POLLIN);
}

// The next two functions implement the "self pipe trick". A pipe is used as
// boolean information whether child processes have terminated. The code is
// "data to read on the pipe" = "child processes have terminated"
static void sigchld_handle(int sig) {
  int saved_errno;
  saved_errno = errno;
  if (write(cpipe[1], "x", 1) == -1 && errno != EAGAIN && errno != EINTR) {
    shutdown_with_msg("error writing to pipe");
  }
  errno = saved_errno;
}

void setup_child_pipe() {
  int flags;
  struct sigaction sa;
  if (pipe(cpipe) == - 1) {
    shutdown_with_msg("error creating pipe");
  }
  flags = fcntl(cpipe[0], F_GETFL);
  if (flags == -1) {
    shutdown_with_msg("error getting flags on pipe");
  }
  flags |= O_NONBLOCK;
  if (fcntl(cpipe[0], F_SETFL, flags) == -1) {
    shutdown_with_msg("error setting flags on pipe");
  }
  flags = fcntl(cpipe[1], F_GETFL);
  if (flags == -1) {
    shutdown_with_msg("error getting flags on pipe");
  }
  flags |= O_NONBLOCK;
  if (fcntl(cpipe[1], F_SETFL, flags) == -1) {
    shutdown_with_msg("error setting flags on pipe");
  }
  sigemptyset(&sa.sa_mask);
  sa.sa_flags = SA_RESTART;
  sa.sa_handler = &sigchld_handle;
  if (sigaction(SIGCHLD, &sa, NULL) == -1) {
    shutdown_with_msg("error installing signal handler");
  }
  add_to_poll_list(cpipe[0], POLLIN);
}

/* Returns the size in bytes of the sun_path field of a struct
   sockaddr_un. This should be defined in macro UNIX_PATH_MAX, which is not
   always defined. */
size_t unix_path_max() {
  return sizeof(struct sockaddr_un) - offsetof(struct sockaddr_un, sun_path);
}

void server_init_listening(char* socketname, int parallel) {
  struct sockaddr_un addr;
  int res;
  int cur_dir;
  char *socketname_copy1, *socketname_copy2, *dirn, *filen;

  // Initialize current_dir pointer. Do that here because we switch the
  // directory temporarily below.
  current_dir = get_cur_dir();

  // Before opening the socket, we switch to the dir of the socket. This
  // workaround is needed because Unix sockets only support relatively short
  // paths (~100 chars depending on the system). We also open a file
  // descriptor to the current dir so that we can switch back afterwards.

  socketname_copy1 = strdup(socketname);
  socketname_copy2 = strdup(socketname);
  dirn = dirname(socketname_copy1);
  filen = basename(socketname_copy2);
  cur_dir = open(".", O_RDONLY);
  if (cur_dir == -1) {
    shutdown_with_msg("error when opening current directory");
  }
  res = chdir(dirn);
  if (res == -1) {
    shutdown_with_msg("error when switching to socket directory");
  }

  init_logging();
  init_request_queue();
  clients = init_list(parallel);
  addr.sun_family = AF_UNIX;
  poll_len = 2 + parallel;
  poll_list = (struct pollfd*) malloc(sizeof(struct pollfd) * poll_len);
  poll_num = 0;
  if (strlen(filen) + 1 > unix_path_max()) {
    shutdown_with_msg("basename of filename too long");
  }
  memcpy(addr.sun_path, filen, strlen(filen) + 1);
  server_sock = socket(AF_UNIX, SOCK_STREAM, 0);
  res = unlink(filen);
  // we delete the file if present
  if (res == -1 && errno != ENOENT) {
    shutdown_with_msg("error deleting socket");
  }
  res = bind(server_sock, (struct sockaddr*) &addr, sizeof(struct sockaddr_un));
  if (res == -1) {
    shutdown_with_msg("error binding socket");
  }
  res = listen(server_sock, parallel*2);
  if (res == -1) {
    shutdown_with_msg("error listening on socket");
  }
  res = fchdir(cur_dir);
  if (res == -1) {
    shutdown_with_msg("error when switching back to current directory");
  }
  res = close(cur_dir);
  if (res == -1) {
    shutdown_with_msg("error closing descriptor to current dir");
  }
  free(socketname_copy1);
  free(socketname_copy2);
  add_to_poll_list(server_sock, POLLIN);
  init_process_list();
  setup_child_pipe();
}

void queue_write(pclient client, char* msgbuf) {
  struct pollfd* entry;
  push_write_data(client->writebuf, msgbuf);
  entry = poll_list_lookup(client->fd);
  if (entry != NULL) {
    entry->events |= POLLOUT;
  }
}

pid_t create_process(char* cmd,
                     int argc,
                     char** argv,
                     bool usestdin,
                     int outfile,
                     int timelimit,
                     int memlimit) {
  struct rlimit res;
  char** unix_argv;
  int count = argc;
  // in the case of usestdin, the last argument is in fact not passed to
  // execvp, it contains the filename instead
  if (usestdin) {
    count--;
  }
  unix_argv = (char**)malloc(sizeof(char*) * (count + 2));
  unix_argv[0] = cmd;
  unix_argv[count + 1] = NULL;
  for (int i = 0; i < count; i++) {
    unix_argv[i + 1] = argv[i];
  }

  pid_t pid = fork ();
  if (pid == -1) {
      shutdown_with_msg("failed to fork");
  }

  // the server process simply collects the created pid and returns
  if (pid > 0) {
    free(unix_argv);
    return pid;
  }

  // we are now in the child, we set the ressource limits and execute the
  // process

  if (timelimit > 0) {
    /* set the CPU time limit */
    getrlimit(RLIMIT_CPU,&res);
    res.rlim_cur = timelimit;
    res.rlim_max = timelimit;
    setrlimit(RLIMIT_CPU,&res);
  }

  if (memlimit > 0) {
    /* set the CPU memory limit */
    getrlimit(RLIMIT_AS,&res);
    res.rlim_cur = memlimit * 1024 * 1024;
    res.rlim_max = memlimit * 1024 * 1024;
    setrlimit(RLIMIT_AS,&res);
  }

  if (timelimit > 0 || memlimit > 0) {
    /* do not generate core dumps */
    getrlimit(RLIMIT_CORE,&res);
    res.rlim_cur = 0;
    res.rlim_max = 0;
    setrlimit(RLIMIT_CORE,&res);
  }

  if (usestdin) {
    int infile = open(argv[count], O_RDONLY);
    if (infile == -1) { perror("Cannot open the input file"); exit(1); }
    dup2(infile, 0);
  }

  //adapt stdout/stderr
  dup2(outfile, 1);
  dup2(outfile, 2);

  /* execute the command */
  execvp(cmd,unix_argv);
  fprintf(stderr, "%s: exec of '%s' failed (%s)\n",
          unix_argv[0],unix_argv[0],strerror(errno));

  exit(1);
}

void write_to_client(pclient client, struct pollfd* entry) {
  char* buf;
  int need_write, has_written;
  buf = prepare_write(client->writebuf, &need_write);
  has_written = write(client->fd, buf, need_write);
  if (has_written != -1) {
    have_written(client->writebuf, has_written);
  }
  if (!has_write_data (client->writebuf)) {
    entry->events &= ~POLLOUT;
  }
}

void send_started_msg_to_client(pclient client,
				char* id) {
   char* msgbuf;
   size_t len = 0;
   int used;
   //len of id + S + semicolon + \n + \0
   len += strlen(id) + 4;
   msgbuf = (char*) malloc(sizeof(char) * len);

   if (msgbuf == NULL) {
      shutdown_with_msg("error when allocating client msg");
   }

   used = snprintf(msgbuf, len, "S;%s\n", id);
   if (used != len - 1) {
      shutdown_with_msg("message for client too long");
   }
   queue_write(client, msgbuf);
}

void send_msg_to_client(pclient client,
                        char* id,
                        int exitcode,
                        double cpu_time,
                        bool timeout,
                        char* outfile) {
   char* msgbuf;
   size_t len = 0;
   int used;
   //len of id + F + 2 semicolon
   len += strlen(id) + 3;
   // we assume a length of at most 9 for both exitcode and time, plus one for
   // the timeout boolean, plus three semicolons, makes 23 chars
   len += 23;
   //len of file + newline + nul
   len+= strlen(outfile) + 1;
   msgbuf = (char*) malloc(sizeof(char) * len);
   if (msgbuf == NULL) {
      shutdown_with_msg("error when allocating client msg");
   }
   used = snprintf(msgbuf, len, "F;%s;%d;%.2f;%d;%s\n",
                   id, exitcode, cpu_time, (timeout?1:0), outfile);
   if (used >= len) {
      shutdown_with_msg("message for client too long");
   }
   queue_write(client, msgbuf);
}

void handle_child_events() {
  pproc child;
  pclient client;
  pid_t  pid;
  double cpu_time;
  int    exit_code;
  bool   is_timeout;
  int status;
  struct rusage usage;

  while (1) {
    pid = wait3(&status, WNOHANG, &usage);
    if (pid <= 0) {
      break;
    }
    cpu_time =
      ((double) usage.ru_utime.tv_sec) +
      ((double) usage.ru_utime.tv_usec / 1000000.0);
    exit_code = 1;
    is_timeout = false;
    if (WIFSIGNALED(status)) {
      is_timeout = true;
      exit_code = WTERMSIG(status);
    } else if (WIFEXITED(status)) {
      exit_code = WEXITSTATUS(status);
    }
    child = (pproc) list_lookup(processes, pid);
    list_remove(processes, pid);
    client = (pclient) list_lookup(clients, child->client_key);
    if (client != NULL) {
      send_msg_to_client(client,
                         child->task_id,
                         exit_code,
                         cpu_time,
                         is_timeout,
                         child->outfile);
    }
    free_process(child);
  }
}

/*@ requires r != NULL && r->req_type == REQ_RUN;
  @*/
void run_request (prequest r) {
  char* outfile;
  int out_descr;
  pproc proc;
  pclient client;
  pid_t id;
  assert (r != NULL);

  client = (pclient) list_lookup(clients, r->key);
  if (client == NULL) {
    return;
  }
  out_descr = open_temp_file(current_dir, &outfile);
  id = create_process(r->cmd,
                      r->numargs,
                      r->args,
                      r->usestdin,
                      out_descr,
                      r->timeout,
                      r->memlimit);
  close(out_descr);

  proc = (pproc) malloc(sizeof(t_proc));
  proc->task_id = r->id;
  proc->client_key = r->key;
  proc->id = id;
  proc->outfile = outfile;
  list_append(processes, id, (void*) proc);
  send_started_msg_to_client(client, r->id);
}

void handle_msg(pclient client, int key) {
  prequest r;
  char* buf;
  int old, cur;
  int max;
  buf = client->readbuf->data;
  max = client->readbuf->len;
  cur = 0;
  old = 0;
  while (cur < max) {
    while (cur < max) {
      if (buf[cur] == '\n')
        break;
      cur++;
    }
    if (cur == max)
      break;
    r = parse_request(buf + old, cur - old, key);
    if (r) {
      switch (r->req_type) {
      case REQ_RUN:
        if (list_length(processes) < parallel) {
          run_request(r);
          free_request(r);
        } else {
          queue_push(queue, (void*) r);
        }
        break;
      case REQ_INTERRUPT:
        // removes all occurrences of r->id from the queue
        log_msg("Why3 server: removing id '%s' from queue",r->id);
        remove_from_queue(r->id);
        kill_processes(r->id);
        free_request(r);
        break;
      }
    }
    //skip newline
    cur++;
    old = cur;
  }
  if (old > 0) {
    have_taken(client->readbuf, old);
  }
}

void shutdown_server() {
  unlink(socketname);
  shutdown_with_msg("last client disconnected");
}

void close_client(pclient client) {
  list_remove(clients, client->fd);
  poll_list_remove(client->fd);
  free_readbuf(client->readbuf);
  free_writebuf(client->writebuf);
  close(client->fd);
  free(client);
  if (single_client && list_is_empty(clients)) {
    shutdown_server();
  }
}


void read_on_client(pclient client) {
  char* buf = prepare_read(client->readbuf, READ_ONCE);
  ssize_t num_read;
  num_read = read(client->fd, buf, READ_ONCE);
  if (num_read == -1) {
    return;
  }
  if (num_read == 0) {
    close_client(client);
    return;
  }
  have_read(client->readbuf, num_read);
  handle_msg(client, client->fd);
}

void schedule_new_jobs() {
  while (list_length(processes) < parallel && !(queue_is_empty (queue))) {
    prequest r = (prequest) queue_pop (queue);
    run_request(r);
    free_request(r);
  }
}

int main(int argc, char **argv) {
  char ch;
  int res;
  struct pollfd* cur;
  pclient client;
  parse_options(argc, argv);
  server_init_listening(socketname, parallel);
  while (1) {
    schedule_new_jobs();
    poll_list_clean();
    while ((res = poll(poll_list, poll_num, -1)) == -1 && errno == EINTR)
      continue;
    if (res == -1) {
      shutdown_with_msg("call to poll failed");
    }
    for (int i = 0; i < poll_num; i++) {
      cur = (struct pollfd*) poll_list + i;
      if (cur->revents == 0) {
        continue;
      }
      // a child has terminated
      if (cur->fd == cpipe[0]) {
        while ((res = read(cpipe[0], &ch, 1)) == -1 && errno == EINTR)
          continue;
        if (res == -1) {
          shutdown_with_msg("call to read shouldn't fail");
        }
        handle_child_events();
        continue;
      }
      // an incoming client
      if (cur->fd == server_sock) {
        assert (cur->revents == POLLIN);
        server_accept_client();
        continue;
      }

      // a client
      client = (pclient) list_lookup(clients, cur->fd);
      if (client == NULL)
        continue;
      if (cur->revents & POLLERR) {
        close_client(client);
      } else if (cur->revents & POLLOUT) {
        write_to_client(client, cur);
      } else if (cur->revents & POLLIN) {
        read_on_client(client);
      }
    }
  }
}

#endif /* _WIN32 */
