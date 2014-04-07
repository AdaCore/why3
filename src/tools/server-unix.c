#include <sys/types.h>
#include <unistd.h>
#include <stdio.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <stdlib.h>
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

#define READ_ONCE 1024

typedef struct {
  int       kind;
  int       fd;
  preadbuf  readbuf;
  pwritebuf writebuf;
} t_client, *pclient;

int server_sock;

typedef struct {
  pid_t id;
  int client_fd;
  char* task_id;
  char* outfile;
} t_proc, *pproc;

struct pollfd* poll_list;
int poll_num = 0;
int poll_len = 0;

plist processes;
plist clients;
char *current_dir;
pqueue queue;

static int cpipe[2];

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
  poll_num++;
}

struct pollfd* poll_list_lookup(int fd) {
  int i;
  for (i = 0; i < poll_num; i++) {
    if (poll_list[i].fd == fd) {
      return poll_list+i;
    }
  }
  return NULL;
}

void poll_list_remove(int fd) {
  int i;
  assert (poll_num > 0);
  for (i = 0; i < poll_num; i++) {
    if (poll_list[i].fd == fd) {
      break;
    }
  }
  if (i == poll_num) {
    return;
  }
  poll_list[i] = poll_list[poll_num - 1];
  poll_num--;
}

int open_temp_file(char* dir, char** outfile) {
  char* template;
  int len;
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
    printf ("error accepting a client\n");
    return;
  }
  client = (pclient) malloc(sizeof(t_client));
  client->fd = fd;
  client->readbuf = init_readbuf(1024);
  client->writebuf = init_writebuf(parallel);
  list_append(clients, fd, (void*)client);
  add_to_poll_list(fd, POLLIN);
}

static void sigchld_handle(int sig) {
  int saved_errno;
  saved_errno = errno;
  if (write(cpipe[1], "x", 1) == -1 && errno != EAGAIN && errno != EINTR) {
    printf("error writing to pipe\n");
  }
  errno = saved_errno;
}

void setup_child_pipe() {
  int flags;
  struct sigaction sa;
  if (pipe(cpipe) == - 1) {
    printf("error creating pipe\n");
    exit(1);
  }
  flags = fcntl(cpipe[0], F_GETFL);
  if (flags == -1) {
    printf("error getting flags on pipe\n");
    exit(1);
  }
  flags |= O_NONBLOCK;
  if (fcntl(cpipe[0], F_SETFL, flags) == -1) {
    printf("error setting flags on pipe\n");
    exit(1);
  }
  flags = fcntl(cpipe[1], F_GETFL);
  if (flags == -1) {
    printf("error getting flags on pipe\n");
    exit(1);
  }
  flags |= O_NONBLOCK;
  if (fcntl(cpipe[1], F_SETFL, flags) == -1) {
    printf("error setting flags on pipe\n");
    exit(1);
  }
  sigemptyset(&sa.sa_mask);
  sa.sa_flags = SA_RESTART;
  sa.sa_handler = sigchld_handle;
  if (sigaction(SIGCHLD, &sa, NULL) == -1) {
    printf("error installing signal handler\n");
    exit(1);
  }
  add_to_poll_list(cpipe[0], POLLIN);
}

void server_init_listening(char* basename, int parallel) {
  struct sockaddr_un addr;
  int res;
  current_dir = get_cur_dir();
  queue = init_queue(100);
  clients = init_list(parallel);
  addr.sun_family = AF_UNIX;
  poll_len = 2 + parallel;
  poll_list = (struct pollfd*) malloc(sizeof(struct pollfd) * poll_len);
  poll_num = 0;
  memcpy(addr.sun_path, basename, strlen(basename) + 1);
  server_sock = socket(AF_UNIX, SOCK_STREAM, 0);
  res = unlink(basename);
  // we delete the file if present, said otherwise we accept ENOENT as error
  if (res == -1 && errno != ENOENT) {
    printf("error binding socket: %d\n", errno);
    exit(1);
  }
  res = bind(server_sock, (struct sockaddr*) &addr, sizeof(struct sockaddr_un));
  if (res == -1) {
    printf("error binding socket: %d\n", errno);
    exit(1);
  }
  res = listen(server_sock, parallel*2);
  if (res == -1) {
    printf("error listening on socket\n");
    exit(1);
  }
  add_to_poll_list(server_sock, POLLIN);
  processes = init_list(parallel);
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
                     int outfile,
                     int timelimit,
                     int memlimit) {
  struct rlimit res;
  int i;
  char** unix_argv;
  unix_argv = (char**)malloc(sizeof(char*) * (argc + 2));
  unix_argv[0] = cmd;
  unix_argv[argc + 1] = NULL;
  for (i = 0; i < argc; i++) {
    unix_argv[i + 1] = argv[i];
  }

  pid_t pid = fork ();
  if (pid == -1) {
      perror("fork");
      exit(EXIT_FAILURE);
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
    setrlimit(RLIMIT_CPU,&res);
  }

  if (memlimit > 0) {
    /* set the CPU memory limit */
    getrlimit(RLIMIT_AS,&res);
    res.rlim_cur = memlimit * 1024 * 1024;
    setrlimit(RLIMIT_AS,&res);
  }

  if (timelimit > 0 || memlimit > 0) {
    /* do not generate core dumps */
    getrlimit(RLIMIT_CORE,&res);
    res.rlim_cur = 0;
    setrlimit(RLIMIT_CORE,&res);
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

void send_msg_to_client(pclient client,
                        char* id,
                        unsigned int exitcode,
                        double cpu_time,
                        bool timeout,
                        char* outfile) {
   char* msgbuf;
   int len = 0;
   //len of id + semicolon
   len += strlen(id) + 1;
   // we assume a length of at most 9 for both exitcode and time, plus one for
   // the timeout boolean, plus three semicolons, makes 23 chars
   len += 23;
   //len of file + newline + nul
   len+= strlen(outfile) + 1;
   msgbuf = (char*) malloc(sizeof(char) * len);
   if (msgbuf == NULL) {
      printf("error when allocating %d\n", len);
      exit(1);
   }
   snprintf(msgbuf, len, "%s;%d;%.2f;%d;%s\n",
      id, exitcode, cpu_time,(timeout?1:0), outfile);
   queue_write(client, msgbuf);
}

void free_process(pproc proc) {
   free(proc->outfile);
   free(proc->task_id);
   free(proc);
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
      ((double)usage.ru_utime.tv_usec / 1000000.0);
    exit_code = 1;
    is_timeout = false;
    if (WIFSIGNALED(status)) {
      is_timeout = true;
    }
    if (WIFEXITED(status)) {
      exit_code = WEXITSTATUS(status);
    }
    child = (pproc) list_lookup(processes, pid);
    list_remove(processes, pid);
    client = (pclient) list_lookup(clients, child->client_fd);
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

void run_request (prequest r) {
  char* outfile;
  int out_descr;
  pproc proc;
  pclient client;
  pid_t id;
  assert (r != NULL);

  client = (pclient) list_lookup(clients, r->key);
  if (client==NULL) {
    return;
  }
  out_descr = open_temp_file(current_dir, &outfile);
  id = create_process(r->cmd,
                      r->numargs,
                      r->args,
                      out_descr,
                      r->timeout,
                      r->memlimit);
  close(out_descr);

  proc = (pproc) malloc(sizeof(t_proc));
  proc->task_id         = r->id;
  proc->client_fd = r->key;
  proc->id = id;
  proc->outfile    = outfile;
  list_append(processes, id, (void*) proc);
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
    r = parse_request(buf+old, cur - old, key);
    if (r) {
      if (list_length(processes) < parallel) {
        run_request(r);
        free_request(r);
      } else {
        queue_push(queue, (void*) r);
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

void close_client(pclient client) {
  list_remove(clients, client->fd);
  poll_list_remove(client->fd);
  free_readbuf(client->readbuf);
  free_writebuf(client->writebuf);
  close(client->fd);
  free(client);
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
    run_request((prequest) queue_pop (queue));
  }
}

int main(int argc, char **argv) {
  int i;
  char ch;
  int res;
  struct pollfd* cur;
  pclient client;
  parse_options(argc, argv);
  server_init_listening(basename, parallel);
  while (1) {
    schedule_new_jobs();
    while ((res = poll(poll_list, poll_num, -1)) == -1 && errno == EINTR)
      continue;
    if (res == -1) {
      exit(1);
    }
    for (i = 0; i < poll_num; i++) {
      cur = (struct pollfd*) poll_list + i;
      if (cur->revents == 0) {
        continue;
      }
      // a child has terminated
      if (cur->fd == cpipe[0]) {
        while ((res = read(cpipe[0], &ch, 1)) == -1 && errno == EINTR)
          continue;
        if (res == -1) {
          exit(1);
        }
        handle_child_events();
        continue;
      }
      // an incoming client
      if (cur->fd == server_sock) {
        assert (cur->revents == POLLIN);
        server_accept_client();
        //we should stop looking at other sockets now, because we have altered
        //the poll list
        break;
      }

      // a client
      client = (pclient) list_lookup(clients, cur->fd);
      if (client == NULL)
        continue;
      if (cur->revents & POLLERR) {
        close_client(client);
      }
      if (cur->revents & POLLOUT) {
        write_to_client(client, cur);
      } else if (cur->revents & POLLIN) {
        read_on_client(client);
      }
    }
  }
}
