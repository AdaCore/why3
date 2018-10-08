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

// This is the windows implementation of the VC server. Its main feature is
// the use of an IO Completion port to handle all kinds of events.
//
// The read/write/connect operations on sockets behave quite differently on
// windows: you need to start them first, and get notified when they are
// terminated.

#ifdef _WIN32

#include <ntstatus.h>
#include <windows.h>
#include <libgen.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <tchar.h>
#include "queue.h"
#include "request.h"
#include "options.h"
#include "readbuf.h"
#include "writebuf.h"
#include "arraylist.h"
#include "logging.h"
#include "proc.h"

#define READ_ONCE 1024
#define BUFSIZE 4096

#define READOP 0
#define WRITEOP 1

// constants to distinguish between events from sockets and processes
#define SOCKET 0
#define PROCESS 1

typedef struct {
   OVERLAPPED overlap;
   int kind;
} t_conn_data, *p_conn_data;

typedef struct {
   HANDLE     handle;
   OVERLAPPED connect;
} t_server, *pserver;

typedef struct {
   int         kind;
   HANDLE      handle;
   t_conn_data read;
   t_conn_data write;
   preadbuf    readbuf;
   pwritebuf   writebuf;
} t_client, *pclient;

// AFAIU, there is no connection queue or something like that, so we need to
// create several socket instances to be able to process several clients that
// would connect almost at the same time. The two variables below will be
// allocated to arrays of equal length, holding the socket handle and the
// "key" (used for IO Completion Port) for each socket instance.
pserver* server_socket;
int* server_key;

plist clients;
char current_dir[MAX_PATH];

int gen_key = 1;

int keygen() {
   return gen_key++;
}

ULONG_PTR to_ms_key(int key, int kind) {
   return key * 2 + kind;
}

int kind_of_ms_key(ULONG_PTR ms) {
   return (ms % 2);
}

int key_of_ms_key(ULONG_PTR ms) {
   return (ms / 2);
}

void init();

char* pipe_name;

HANDLE completion_port;

void shutdown_with_msg(char* msg);

void shutdown_with_msg(char* msg) {
  if (completion_port != NULL) {
    CloseHandle (completion_port);
  }
  for (int i = 0; i < parallel; i++) {
     if (server_socket[i] != NULL) {
       CloseHandle (server_socket[i]->handle);
     }
  }
  if (clients != NULL) {
     for (int i = 0; i < list_length(clients); i++) {
       CloseHandle(((pclient) clients->data[i])->handle);
     }
  }
  if (processes != NULL) {
     for (int i = 0; i < list_length(processes); i++) {
       free_process(processes->data[i]);
     }
  }
  logging_shutdown(msg);
}

void send_msg_to_client(pclient client,
                        char* id,
                        DWORD exitcode,
                        double cpu_time,
                        bool timeout,
                        char* outfile);
//send msg to [client] about the result of VC [id]
//
void send_started_msg_to_client(pclient client, char* id);
//send msg to [client] that the VC [id] has been started

void add_to_completion_port(HANDLE h, ULONG_PTR key) {
   HANDLE tmp = CreateIoCompletionPort(h, completion_port, key, 1);
   if (tmp == NULL) {
     shutdown_with_msg("CreateIoCompletionPort: error adding handle");
   }
   if (completion_port == NULL) {
      completion_port = tmp;
   }
}

void init_connect_data(t_conn_data* data, int kind) {
   ZeroMemory(data, sizeof(t_conn_data));
   data->overlap.hEvent = CreateEvent(NULL, FALSE, TRUE, NULL);
   data->kind = kind;
}

void try_write(pclient client) {
   int num_write;
   DWORD num_written;
   char* buf;
   if (has_write_data (client->writebuf) &&
       can_write(client->writebuf)) {
      buf = prepare_write(client->writebuf, &num_write);
      WriteFile (client->handle,
                 buf,
                 num_write,
                 &num_written,
                 (LPOVERLAPPED) &client->write);
   }
}

// create a server socket and store it in the ith component of the
// server_socket array
void create_server_socket (int socket_num) {
   pserver server;
   int key = keygen();
   server = (pserver) malloc(sizeof(t_server));
   server->handle = CreateNamedPipe(
      pipe_name,
      PIPE_ACCESS_DUPLEX |
      FILE_FLAG_OVERLAPPED,     // non-blocking IO
      PIPE_TYPE_MESSAGE |       // message-type pipe
      PIPE_READMODE_MESSAGE |   // message read mode
      PIPE_WAIT,                // blocking mode
      PIPE_UNLIMITED_INSTANCES, // number of instances
      BUFSIZE*sizeof(TCHAR),    // output buffer size
      BUFSIZE*sizeof(TCHAR),    // input buffer size
      5000,                     // client time-out
      NULL);
   if (server->handle == INVALID_HANDLE_VALUE) {
      exit(1);
   }
   add_to_completion_port(server->handle, to_ms_key(key, SOCKET));
   ZeroMemory(&server->connect, sizeof(OVERLAPPED));
   server->connect.hEvent = CreateEvent(NULL, FALSE, TRUE, NULL);
   server_socket[socket_num] = server;
   server_key[socket_num] = key;
   if (!ConnectNamedPipe(server->handle, (LPOVERLAPPED) &server->connect)) {
      DWORD err = GetLastError();
      if (err == ERROR_IO_PENDING) {
         //this is the state we want: server socket is waiting
         return;
      } else if (err == ERROR_PIPE_CONNECTED) {
        //connection works, ignore
        ;
      } else {
        shutdown_with_msg("error connecting to socket");
      }
   }
}

HANDLE open_temp_file(char** outfile) {
   HANDLE h;
   SECURITY_ATTRIBUTES saAttr;
   DWORD res;
   // allow the handle to the temp file to be inherited by child processes
   // using security attributes
   saAttr.nLength = sizeof(SECURITY_ATTRIBUTES);
   saAttr.bInheritHandle = TRUE;
   saAttr.lpSecurityDescriptor = NULL;
   *outfile = (char*) malloc (sizeof(char) * MAX_PATH);
   res = GetTempFileName(current_dir, TEXT("vcout"), 0, *outfile);
   if (res ==0) {
     shutdown_with_msg("error obtaining a tmp file name");
   }
   h = CreateFile(*outfile,
                  GENERIC_WRITE,
                  0,
                  &saAttr,
                  CREATE_ALWAYS,
                  FILE_ATTRIBUTE_NORMAL,
                  NULL);
   if (h == INVALID_HANDLE_VALUE) {
      shutdown_with_msg("error creating a tmp file");
   }
   return h;
}

void run_request (prequest r) {
   char cmd[4096];
   char* outfile;
   pproc proc;
   int key;
   int argcount = r->numargs;
   JOBOBJECT_EXTENDED_LIMIT_INFORMATION limits;
   JOBOBJECT_ASSOCIATE_COMPLETION_PORT portassoc;
   STARTUPINFO si;
   HANDLE ghJob, outfilehandle, infilehandle;
   PROCESS_INFORMATION pi;
   pclient client;

  // in the case of usestdin, the last argument is in fact not passed to
  // CreateProcess, it contains the filename instead
   if (r->usestdin) {
     argcount--;
   }

   client = (pclient) list_lookup(clients, r->key);
   if (client==NULL) {
      return;
   }
   ghJob = CreateJobObject(NULL,NULL);
   if (ghJob == NULL) {
     shutdown_with_msg("failed creating job object");
   }
   ZeroMemory(&si, sizeof(si));
   si.cb = sizeof(si);
   ZeroMemory(&pi, sizeof(pi));
   outfilehandle = open_temp_file(&outfile);
   // set the stdout for the childprocess
   si.hStdOutput = outfilehandle;
   si.hStdError = outfilehandle;
   if (r->usestdin) {
     infilehandle =
       CreateFile(r->args[argcount],
                 GENERIC_READ,
                 FILE_SHARE_READ,
                 NULL,
                 OPEN_ALWAYS,
                 FILE_ATTRIBUTE_NORMAL,
                 NULL);
     si.hStdInput = infilehandle;
   }
   // if we don't set that flag, the stdout we just set won't even be looked at
   si.dwFlags = STARTF_USESTDHANDLES;
   /* Compute command line string. When a parameter contains a " or a space we
      should quote it with doublequotes.  Double quotes inside the string should
      be escaped by a backslash.  All backslashes precedind a " should also be
      escaped.  */

   /* First copy the command name */
   strcpy (cmd, r->cmd);
   strcat (cmd, " ");

   /* Now take care of the arguments */
   {
     for (int k = 0; k < argcount; k++)
       {
         char *ca = r->args[k]; /* current arg */
         int need_quote = 1; /* set to 1 if quotes are needed */

         /* Should we quote the string ? */
         if (strlen(ca) > 0)
            need_quote = 0;

         for (int ca_index = 0; ca_index < strlen(ca); ca_index++)
           {
             if (ca[ca_index] == ' ' || ca[ca_index] == '"')
               {
                 need_quote = 1;
                 break;
               }
           }

         /* Do quoting if necessary. Note it is important not to quote
            arguments that do not need it as some buggy implementations
            such vxsim will see for example -p as "-p" :-). */
         if (need_quote == 1)
           {
             int cl_index = strlen(cmd);

             /* Open the double quoted string */
             cmd[cl_index] = '"'; cl_index++;

             for (int ca_index = 0; ca_index < strlen(ca); ca_index++)
               {

                 /* We have a double in the argument. It should be escaped
                    along with all previous backslashes.  */
                 if (ca[ca_index] == '"')
                   {
                     /* We have blackslashes before the double quote.
                        They should be quoted.  */
                     if (ca_index > 0 && ca[ca_index - 1] == '\\')
                       {
                         for (int j = ca_index - 1; j >= 0 && ca[j] == '\\' ;j--)
                           {
                             cmd[cl_index] = '\\'; cl_index++;
                           }
                       }

                     cmd[cl_index] = '\\'; cl_index++;
                     cmd[cl_index] = '"';  cl_index++;
                   }
                 else
                   {
                     /* This is not a double quote so just add the character */
                     cmd[cl_index] = ca[ca_index]; cl_index++;

                     /* We have blackslashes before the ending double quote.
                        They should be quoted.  */
                     if (ca[ca_index] == '\\' && ca_index + 1 == strlen(ca))
                       {
                         for (int j = ca_index; j >= 0 && ca[j] == '\\' ;j--)
                           {
                             cmd[cl_index] = '\\'; cl_index++;
                           }
                       }
                   }
               }

             /* Close the doublequoted string */
             cmd[cl_index] = '"'; cl_index++;
             cmd[cl_index] = ' '; cl_index++;
             cmd[cl_index] = '\0';
           }
         else
           /* The argument does not need quoting. Just append it to the command
              line */
           {
             strcat (cmd, ca);
             strcat (cmd, " ");
           }
       }
   }
   if (r->timeout!=0||r->memlimit!=0) {
     ULONGLONG timeout;
     ZeroMemory(&limits, sizeof(limits));
     limits.BasicLimitInformation.LimitFlags =
       ((r->timeout==0)?0:JOB_OBJECT_LIMIT_PROCESS_TIME)
       |((r->memlimit==0)?0:JOB_OBJECT_LIMIT_PROCESS_MEMORY);

     // seconds to W32 kernel ticks
     if (r->timeout!=0) {
       timeout = 1000ULL * 1000ULL * 10ULL * r->timeout;
       limits.BasicLimitInformation.PerProcessUserTimeLimit.QuadPart=timeout;
     }
     if (r->memlimit!=0) {
       size_t memory = 1024 * 1024 * r->memlimit;
       limits.ProcessMemoryLimit = memory;
     }

     if (!SetInformationJobObject(ghJob, JobObjectExtendedLimitInformation,
 				 &limits, sizeof(limits))) {
       shutdown_with_msg("error in SetInformationJobObject");
     }
   }

   // launches "child" process with command line parameter
   if(!CreateProcess(NULL,
                     cmd,
                     NULL,
                     NULL,
                     TRUE,
                     CREATE_SUSPENDED | CREATE_BREAKAWAY_FROM_JOB,
                     NULL,
                     NULL,
                     &si,
                     &pi)) {
       log_msg("%s",cmd);
       CloseHandle(outfilehandle);
       CloseHandle(ghJob);
       send_msg_to_client(client,
                          r->id,
                          0,
                          0,
                          0,
                          outfile);
      return;
   }
   if (!AssignProcessToJobObject(ghJob,pi.hProcess)) {
     shutdown_with_msg("failed to assign process to job object");
   }
   proc = (pproc) malloc(sizeof(t_proc));
   proc->handle     = pi.hProcess;
   proc->job        = ghJob;
   proc->task_id    = r->id;
   proc->client_key = r->key;
   proc->outfile    = outfile;
   key              = keygen();
   list_append(processes, key, (void*) proc);
   send_started_msg_to_client(client, r->id);
   portassoc.CompletionKey = (void*) to_ms_key(key, PROCESS);
   portassoc.CompletionPort = completion_port;
   if (!SetInformationJobObject
         (ghJob,
          JobObjectAssociateCompletionPortInformation,
          &portassoc,
          sizeof( portassoc ) ) ) {
     shutdown_with_msg( "Could not associate job with IO completion port");
   }

   /* Let's resume the process */
   ResumeThread(pi.hThread);
   //we don't need these handles any more
   CloseHandle(outfilehandle);
   CloseHandle(pi.hThread);
}

void handle_msg(pclient client, int key) {
   prequest r;
   //the read buffer also contains the newline, skip it
   r = parse_request(client->readbuf->data, client->readbuf->len - 1, key);
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
        remove_from_queue(r->id);
        kill_processes(r->id);
        // no need to clean up the list of processes and free the memory for
        // processes, this will be done when we get notified of the end of the
        // child process
        free_request(r);
        break;
      }
   }
}

void do_read(pclient client) {
   DWORD has_read;
   char* buf = prepare_read(client->readbuf, READ_ONCE);
   ReadFile(client->handle,
            buf,
            READ_ONCE,
            &has_read,
            (LPOVERLAPPED) &client->read);
}

// the server socket with [key] and whose handle is stored in the [socket_num]
// component of the server_socket array, has received a client request. Handle
// it and create a new server socket instance for this socket number
void accept_client(int key, int socket_num) {
   pclient client = (pclient) malloc(sizeof(t_client));
   client->handle = server_socket[socket_num]->handle;
   client->readbuf = init_readbuf(BUFSIZE);
   client->writebuf = init_writebuf(16);
   init_connect_data(&(client->read), READOP);
   init_connect_data(&(client->write), WRITEOP);
   free(server_socket[socket_num]);
   create_server_socket(socket_num);
   list_append(clients, key, (void*)client);
   do_read(client);
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
   push_write_data(client->writebuf, msgbuf);
   try_write(client);
}


void send_msg_to_client(pclient client,
                        char* id,
                        DWORD exitcode,
                        double cpu_time,
                        bool timeout,
                        char* outfile) {
   char* msgbuf;
   int len = 0;
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
     shutdown_with_msg("error when allocating buffer for client msg");
   }
   used = snprintf(msgbuf, len, "F;%s;%lu;%.2f;%d;%s\n",
                   id, exitcode, cpu_time, (timeout?1:0), outfile);
   if (used >= len) {
      shutdown_with_msg("message for client too long");
   }
   push_write_data(client->writebuf, msgbuf);
   try_write(client);
}

void shutdown_server() {
  shutdown_with_msg("last client disconnected");
}

void close_client(pclient client, int key) {
  list_remove(clients, key);
  CloseHandle(client->handle);
  free_readbuf(client->readbuf);
  free_writebuf(client->writebuf);
  free(client);
  if (single_client && list_is_empty(clients)) {
    shutdown_server();
  }
}

void schedule_new_jobs() {
  while (list_length(processes) < parallel && !(queue_is_empty (queue))) {
    prequest r = (prequest) queue_pop (queue);
    run_request(r);
    free_request(r);
  }
}

void handle_child_event(pproc child, pclient client, int proc_key, DWORD event) {
   DWORD exitcode;
   bool timeout;
   FILETIME ft_start, ft_stop, ft_system, ft_user;
   ULARGE_INTEGER ull_system, ull_user;
   double cpu_time;
   switch (event) {
      //the first two events can be safely ignored
      case JOB_OBJECT_MSG_NEW_PROCESS:
      case JOB_OBJECT_MSG_ACTIVE_PROCESS_ZERO:
         return;

      //violation of some limit
      case JOB_OBJECT_MSG_END_OF_JOB_TIME:
      case JOB_OBJECT_MSG_END_OF_PROCESS_TIME:
      case JOB_OBJECT_MSG_JOB_MEMORY_LIMIT:
      case JOB_OBJECT_MSG_PROCESS_MEMORY_LIMIT:
      //some error
      case JOB_OBJECT_MSG_ABNORMAL_EXIT_PROCESS:
      //normal exit
      case JOB_OBJECT_MSG_EXIT_PROCESS:
         // This wait is necessary to be sure that the handles of the child
         // process have been closed. In measurements, the wait takes a couple
         // of milliseconds.
         WaitForSingleObject(child->handle, INFINITE);
         list_remove(processes, proc_key);
         GetExitCodeProcess(child->handle, (LPDWORD) &exitcode);
         GetProcessTimes(child->handle, &ft_start, &ft_stop, &ft_system, &ft_user);
         ull_system.LowPart = ft_system.dwLowDateTime;
         ull_system.HighPart = ft_system.dwHighDateTime;
         ull_user.LowPart = ft_user.dwLowDateTime;
         ull_user.HighPart = ft_user.dwHighDateTime;
         cpu_time =
           ((ull_system.QuadPart + ull_user.QuadPart + 0.0) / 10000000.);
         timeout = (exitcode == ERROR_NOT_ENOUGH_QUOTA) ||
                   (exitcode == STATUS_QUOTA_EXCEEDED);
         send_msg_to_client(client,
                            child->task_id,
                            exitcode,
                            cpu_time,
                            timeout,
                            child->outfile);
         free_process(child);
         break;
      default:
         exit(1);
   }
}

void init() {
   // The socketname variable may contain a full path, but on Windows,
   // pipe sockets live in a special address space. We throw away the
   // path info and just use the basename of the socketname variable.
   char* socketname_copy, *my_pipe_name;
   GetCurrentDirectory(MAX_PATH, current_dir);
   socketname_copy = strdup(socketname);
   my_pipe_name = basename(socketname_copy);
   // on windows, named pipes live in a special address space
   pipe_name = (char*) malloc(sizeof(char) * (strlen(my_pipe_name) + 10));
   strcpy(pipe_name, TEXT("\\\\.\\pipe\\"));
   strcat(pipe_name, my_pipe_name);

   init_request_queue();
   clients = init_list(parallel);
   init_process_list();

   server_socket = (pserver*) malloc(parallel * sizeof(pserver));
   server_key = (int*) malloc(parallel * sizeof(int));

   init_logging();
   for (int i = 0; i < parallel; i++) {
      create_server_socket(i);
   }
   free(socketname_copy);
}

// If the key in argument corresponds to a server socket, return the server
// socket number, else return -1.
int get_server_num (int key) {
   for (int i=0; i < parallel; i++) {
      if (server_key[i] == key)
         return i;
   }
   return -1;
}

int main(int argc, char **argv) {
   DWORD numbytes;
   ULONG_PTR mskey;
   int key;
   int kind;
   int server_num;
   LPOVERLAPPED ov;
   p_conn_data conn;
   BOOL res;
   pclient client;
   pproc proc;
   // We set the error mode here. This avoids pop-ups when the process
   // crashes. Also, this setting will be inherited by prover processes, so
   // that they don't open pop-ups either in case of crash.
   SetErrorMode(SEM_FAILCRITICALERRORS | SEM_NOGPFAULTERRORBOX);
   parse_options(argc, argv);
   init();
   while (1) {
      schedule_new_jobs();
      res = GetQueuedCompletionStatus(completion_port,
                                      &numbytes,
                                      &mskey,
                                      &ov,
                                      INFINITE);
      if (mskey == 0) {
        shutdown_with_msg("GetQueuedCompletionStatus failed");
      }
      key = key_of_ms_key(mskey);
      kind = kind_of_ms_key(mskey);
      server_num = get_server_num(key);
      switch (kind) {
         case SOCKET:
            if (server_num != -1) {
               if (!res && GetLastError () != ERROR_PIPE_CONNECTED) {
                  shutdown_with_msg("error connecting client");
               } else {
                  accept_client(key, server_num);
               }
               break;
            }
            client = (pclient) list_lookup(clients, key);
            if (client == NULL) {
               //client already dead, ignore any events
               break;
            }
            conn = (p_conn_data) ov;
            switch (conn->kind) {
               case READOP:
                  have_read(client->readbuf, numbytes);
                  if (res) {
                     // we can be sure that we have read a single message
                     // entirely, that's how ReadFile works on pipes
                     handle_msg(client, key);
                     clear_readbuf(client->readbuf);
                     do_read(client);
                  } else if
                     (numbytes == 0 && GetLastError() == ERROR_BROKEN_PIPE) {
                     close_client(client, key);
                  } else {
                     do_read(client);
                  }
                  break;
               case WRITEOP:
                  have_written(client->writebuf, numbytes);
                  try_write(client);
                  break;
               default:
                  exit(1);
            }
            break;
         case PROCESS:
            proc = (pproc) list_lookup(processes, key);
            if (proc != NULL) {
               client = (pclient) list_lookup(clients, proc->client_key);
               if (client != NULL) {
                  handle_child_event(proc, client, key, numbytes);
               }
            }
            break;
         default:
            exit(1);

      }
   }
}

#endif /* _WIN32 */
