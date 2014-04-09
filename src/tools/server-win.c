// This is a VC server for Why3. It implements the following functionalities:
// * wait for connections on a unix domain socket (unix) or named pipe
//   (windows) for clients
// * clients can send requests for a process to spawn, including
//   timeout/memory limit
// * server will send back a filename containing the output of the process,
//   as well as the time taken and the exit code
//
// Command line options
// ====================
//
//    -j <n>      the maximum number of processes to spawn in parallel
//    --socket    the name of the socket or named pipe
//
//  Protocol
// =========
//
// A client request is a single line which looks like this:
//
//   id;timeout;memlimit;cmd;arg1;arg2;...;argn
//
// All items are separated by semicolons, and must not contain semicolons
// themselves (but may contain spaces). Their meaning is the following:
//   id       - a (ideally) unique identifier which identifies the request
//   timeout  - the allowed CPU time in seconds for this command;
//              this must be number, 0 for unlimited
//   memlimit - the allowed consumed memory for this command
//              this must be number, 0 for unlimited
//   cmd      - the name of the executable to run
//   arg(i)   - the commandline arguments of the command to run
//
// A server answer looks like this:
//
//   id;exitcode;time;timeout;file
//
// Their meaning is the following:
//   id       - the identifier of the request to which this answer belongs
//   exitcode - the exitcode of the executed program
//   time     - the time taken by the executed program
//   timeout  - 0 for regular exit or crash, 1 for program interrupt through
//              timeout
//   file     - the path to a file which contains the stdout and stderr of the
//              executed program

#include <windows.h>
#include <stdio.h>
#include <stdlib.h>
#include <tchar.h>
#include <assert.h>
#include "queue.h"
#include "request.h"
#include "options.h"
#include "readbuf.h"
#include "writebuf.h"
#include "arraylist.h"

#define READ_ONCE 1024
#define BUFSIZE 4096

#define READOP 0
#define WRITEOP 1

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

typedef struct {
   HANDLE handle;
   HANDLE job;
   int client_key;
   char* id;
   char* outfile;
} t_proc, *pproc;

pserver server_socket;
int server_key = 0;
plist clients;
plist processes;
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

static void
ErrorReport(char *function)
{
    char *message;
    DWORD error = GetLastError();

    FormatMessage(
                  FORMAT_MESSAGE_ALLOCATE_BUFFER |
                  FORMAT_MESSAGE_FROM_SYSTEM,
                  NULL,
                  error,
                  MAKELANGID(LANG_NEUTRAL, SUBLANG_DEFAULT),
                  (LPTSTR) &message,
                  0, NULL );

    printf("Fatal: %s failed with error %ld: %s",
           function, error, message);
    LocalFree(message);
}

void init();

char* socket_name = NULL;

HANDLE completion_port = NULL;

void add_to_completion_port(HANDLE h, ULONG_PTR key) {
   HANDLE tmp = CreateIoCompletionPort(h, completion_port, key, 1);
   if (tmp == NULL) {
      ErrorReport("CreateIoCompletionPort");
      printf("error adding handle to completion port\n");
      exit(1);
   }
   if (completion_port == NULL) {
      completion_port = tmp;
   }
}

pqueue queue;

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

void create_server_socket () {
   pserver server;
   int key = keygen();
   server = (pserver) malloc(sizeof(t_server));
   server->handle = CreateNamedPipe(
      socket_name,
      PIPE_ACCESS_DUPLEX |
      FILE_FLAG_OVERLAPPED,     // non-blocking IO
      PIPE_TYPE_MESSAGE |       // message-type pipe
      PIPE_READMODE_MESSAGE |   // message read mode
      PIPE_WAIT,                // blocking mode
      PIPE_UNLIMITED_INSTANCES,       // number of instances
      BUFSIZE*sizeof(TCHAR),       // output buffer size
      BUFSIZE*sizeof(TCHAR),       // input buffer size
      5000,                     // client time-out
      NULL);
   if (server->handle == INVALID_HANDLE_VALUE) {
      exit(1);
   }
   add_to_completion_port(server->handle, to_ms_key(key, SOCKET));
   ZeroMemory(&server->connect, sizeof(OVERLAPPED));
   server->connect.hEvent = CreateEvent(NULL, FALSE, TRUE, NULL);
   server_socket = server;
   server_key = key;
   if (!ConnectNamedPipe(server->handle, (LPOVERLAPPED) &server->connect)) {
      DWORD err = GetLastError();
      if (err == ERROR_IO_PENDING) {
         //this is the state we want: server socket is waiting
         return;
      } else if (err == ERROR_PIPE_CONNECTED) {
         //connection works, ignore
         printf("pipe already connected\n");
         ;
      } else {
         printf("error connecting to socket\n");
         exit(1);
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
      printf("error obtaining a tmp file name\n");
      exit(1);
   }
   h = CreateFile(*outfile,
                  GENERIC_WRITE,
                  0,
                  &saAttr,
                  CREATE_ALWAYS,
                  FILE_ATTRIBUTE_NORMAL,
                  NULL);
   if (h == INVALID_HANDLE_VALUE) {
      printf("error creating a tmp file: %ld\n", GetLastError());
      exit(1);
   }
   return h;
}

void run_request (prequest r) {
   unsigned int cmdlen = 0;
   int i;
   char* cmd;
   char* outfile;
   pproc proc;
   int key;
   JOBOBJECT_EXTENDED_LIMIT_INFORMATION limits;
   JOBOBJECT_ASSOCIATE_COMPLETION_PORT portassoc;
   STARTUPINFO si;
   HANDLE ghJob, outfilehandle;
   PROCESS_INFORMATION pi;
   pclient client;

   client = (pclient) list_lookup(clients, r->key);
   if (client==NULL) {
      return;
   }
   ghJob = CreateJobObject(NULL,NULL);
   // ??? check return value of CreateJobObject
   ZeroMemory(&si, sizeof(si));
   si.cb = sizeof(si);
   ZeroMemory(&pi, sizeof(pi));
   cmdlen += strlen(r->cmd) + 3;
   for (i = 0; i < r->numargs; i++) {
      cmdlen += strlen(r->args[i]) + 3;
   }
   // CreateProcess does not allow more than 32767 bytes for command line parameter
   if (cmdlen > 32767) {
     printf("Error: parameter's length exceeds CreateProcess limits\n");
     exit(1);
   }
   cmd = (char*) malloc(sizeof(char) * cmdlen + 1);
   if (cmd == NULL) {
     printf("Error: when allocating %d bytes in memory\n", (int) cmdlen);
     exit(1);
   }
   outfilehandle = open_temp_file(&outfile);
   // set the stdout for the childprocess
   si.hStdOutput = outfilehandle;
   si.hStdError = outfilehandle;
   // if we don't set that flag, the stdout we just set won't even be looked at
   si.dwFlags = STARTF_USESTDHANDLES;
   *cmd = '\0';
   strcat(cmd, "\"");
   strcat(cmd, r->cmd);
   strcat(cmd, "\"");
   strcat(cmd, " ");
   // ??? fix escaping of command line, see N409-041
   for (i = 0; i < r->numargs; i++) {
     strcat(cmd, "\"");
     strcat(cmd, r->args[i]);
     strcat(cmd, "\"");
     if (i < r->numargs - 1) strcat(cmd, " ");
   }
   if (r->timeout!=0||r->memlimit!=0)
     {/* Set the time limit */
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
       printf("error in SetInformationJobObject\n");
       exit(1);
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
       printf( "Error: failed when launching <%s>\n", cmd);
       printf("error in CreateProcess\n");
       exit(1);
   }
   if (!AssignProcessToJobObject(ghJob,pi.hProcess)) {
       printf("error in AssignProcessToJobObject\n");
       exit(1);
   }
   proc = (pproc) malloc(sizeof(t_proc));
   proc->handle     = pi.hProcess;
   proc->job        = ghJob;
   proc->id         = r->id;
   proc->client_key = r->key;
   proc->outfile    = outfile;
   key              = keygen();
   list_append(processes, key, (void*) proc);
   portassoc.CompletionKey = (void*) to_ms_key(key, PROCESS);
   portassoc.CompletionPort = completion_port;
   if (!SetInformationJobObject
         (ghJob,
          JobObjectAssociateCompletionPortInformation,
          &portassoc,
          sizeof( portassoc ) ) ) {
      wprintf( L"Could not associate job with IO completion port, error %d\n", GetLastError() );
      exit(1);
   }
   free(cmd);

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
      if (list_length(processes) < parallel) {
        run_request(r);
        free_request(r);
      } else {
         queue_push(queue, (void*) r);
      }
   }
}

void do_read(pclient client) {
   DWORD has_read;
   char* buf = prepare_read(client->readbuf, READ_ONCE);
   !ReadFile(client->handle,
             buf,
             READ_ONCE,
             &has_read,
             (LPOVERLAPPED) &client->read);
}

void accept_client(int key) {
   pclient client = (pclient) malloc(sizeof(t_client));
   client->handle = server_socket->handle;
   client->readbuf = init_readbuf(BUFSIZE);
   client->writebuf = init_writebuf(parallel);
   init_connect_data(&(client->read), READOP);
   init_connect_data(&(client->write), WRITEOP);
   free(server_socket);
   create_server_socket();
   list_append(clients, key, (void*)client);
   do_read(client);
}

void free_process(pproc proc) {
   CloseHandle(proc->handle);
   CloseHandle(proc->job);
   free(proc->id);
   free(proc->outfile);
   free(proc);
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
   push_write_data(client->writebuf, msgbuf);
   try_write(client);
}

void close_client(pclient client, int key) {
   list_remove(clients, key);
   CloseHandle(client->handle);
   free_readbuf(client->readbuf);
   free_writebuf(client->writebuf);
   free(client);
}

void schedule_new_jobs() {
   while (list_length(processes) < parallel && !(queue_is_empty (queue))) {
      run_request((prequest) queue_pop (queue));
   }
}

void handle_child_event(pproc child, pclient client, int proc_key, DWORD event) {
   unsigned int exitcode;
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
         send_msg_to_client(client,
                            child->id,
                            exitcode,
                            cpu_time,
                            (exitcode == 1816),
                            child->outfile);
         free_process(child);
         break;
      default:
         exit(1);
   }
}

void init() {
   GetCurrentDirectory(MAX_PATH, current_dir);
   // on windows, named pipes live in a special address space
   socket_name = (char*) malloc(sizeof(char) * (strlen(basename) + 10));
   strcpy(socket_name, TEXT("\\\\.\\pipe\\"));
   strcat(socket_name, basename);

   queue = init_queue(100);
   clients = init_list(parallel);
   processes = init_list(parallel);

   create_server_socket();
}

int main(int argc, char **argv) {
   DWORD numbytes;
   ULONG_PTR mskey;
   int key;
   int kind;
   LPOVERLAPPED ov;
   p_conn_data conn;
   BOOL res;
   pclient client;
   pproc proc;
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
         printf("wait failed: %ld\n", GetLastError());
         exit(1);
      }
      key = key_of_ms_key(mskey);
      kind = kind_of_ms_key(mskey);
      switch (kind) {
         case SOCKET:
            if (key == server_key) {
               if (!res && GetLastError () != ERROR_PIPE_CONNECTED) {
                  printf("error connecting client %ld\n", GetLastError());
               } else {
                  accept_client(key);
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
