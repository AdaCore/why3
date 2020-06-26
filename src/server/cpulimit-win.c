/********************************************************************/
/*                                                                  */
/*  The Why3 Verification Platform   /   The Why3 Development Team  */
/*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  */
/*                                                                  */
/*  This software is distributed under the terms of the GNU Lesser  */
/*  General Public License version 2.1, with the special exception  */
/*  on linking described in file LICENSE.                           */
/*                                                                  */
/********************************************************************/

/* $Id: cpulimit-win.c,v 1.3 2009-12-09 08:28:00 nrousset Exp $ */

#ifdef _WIN32

#include <windows.h>
#include <stdlib.h>
#include <stdio.h>
#include <errno.h>
#include <string.h>

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

static PROCESS_INFORMATION pi;
static HANDLE ghJob;

void terminates(void) {
  TerminateProcess(pi.hProcess, 10);
  CloseHandle(pi.hProcess);
  CloseHandle(pi.hThread);
  CloseHandle(ghJob);
}
BOOL WINAPI ConsoleHandler(DWORD CEvent)
{
    /*    switch(CEvent)
    {
    case CTRL_C_EVENT:
    case CTRL_BREAK_EVENT:
    case CTRL_CLOSE_EVENT:
    case CTRL_LOGOFF_EVENT:
    case CTRL_SHUTDOWN_EVENT:*/
  printf("Got signal from console: killing subprocess\n");
  fflush(stdout);
  terminates();
  return TRUE;
}

int main(int argc, char *argv[]) {
  STARTUPINFO si;
  FILETIME ft_start, ft_stop, ft_system, ft_user;
  ULARGE_INTEGER ull_start, ull_stop, ull_system, ull_user;
  double cpu_time, wall_time;
  int i,showtime,hidetime;
  unsigned ex;
  unsigned long s = 0; // length of args after concat
  char * p; // command line parameter
  long long time_limit_seconds=0,memory_limit_MiB=0;
  unsigned error = 0;
  JOBOBJECT_EXTENDED_LIMIT_INFORMATION limits;
  ghJob = CreateJobObject(NULL,NULL);
  if(!ghJob) ErrorReport("CreateJobObject");
  ZeroMemory(&si, sizeof(si));
  si.cb = sizeof(si);
  ZeroMemory(&pi, sizeof(pi));
  SetConsoleCtrlHandler(&ConsoleHandler,TRUE);

  if (argc<5) error=1;
  else {
    time_limit_seconds = strtol (argv[1], &p, 10);
    if (*p!='\0') error=1;
    memory_limit_MiB = strtol (argv[2], &p, 10);
    if (*p!='\0') error=1;
    showtime = !strncmp("-s",argv[3],3);
    hidetime = !strncmp("-h",argv[3],3);
  }

  if (error || !(showtime || hidetime)) {
    fprintf(stderr, "usage: %s <time limit in seconds> <virtual memory limit in MiB>\n"
                    "          <show/hide cpu time: -s|-h> <command> <args>...\n\n"
                    "Zero sets no limit (keeps the actual limit)\n", argv[0]);
    return EXIT_FAILURE;
  }
  // concats argv[4..] into a single command line parameter and puts quotes around arguments
  for (i = 4; i < argc; i++)
    s += strlen(argv[i]) + 3;
  // CreateProcess does not allow more than 32767 bytes for command line parameter
  if (s > 32767) {
    printf("%s: Error: parameter's length exceeds CreateProcess limits\n", argv[0]);
    return EXIT_FAILURE;
  }
  p = (char*) malloc(s);
  if (p == NULL) {
    printf("%s: Error: when allocating %d bytes in memory\n", argv[0], (int) s);
    return EXIT_FAILURE;
  }
  *p = '\0';
  for (i = 4; i < argc; i++) {
    strcat(p, "\"");
    strcat(p, argv[i]);
    strcat(p, "\"");
    if (i < argc - 1) strcat(p, " ");
  }

  if (time_limit_seconds!=0||memory_limit_MiB!=0)
    {/* Set the time limit */
    ULONGLONG timeout;
    ZeroMemory(&limits, sizeof(limits));
    limits.BasicLimitInformation.LimitFlags =
      ((time_limit_seconds==0)?0:JOB_OBJECT_LIMIT_PROCESS_TIME)
      |((memory_limit_MiB==0)?0:JOB_OBJECT_LIMIT_PROCESS_MEMORY);

    // seconds to W32 kernel ticks
    if (time_limit_seconds!=0) {
      timeout = 1000ULL * 1000ULL * 10ULL * time_limit_seconds;
      limits.BasicLimitInformation.PerProcessUserTimeLimit.QuadPart=timeout;
    }
    if (memory_limit_MiB!=0) {
      size_t memory = 1024 * 1024 * memory_limit_MiB;
      limits.ProcessMemoryLimit = memory;
    }

    if (!SetInformationJobObject(ghJob, JobObjectExtendedLimitInformation,
				 &limits, sizeof(limits))) {
      ErrorReport("SetInformationJobObject");
      return EXIT_FAILURE;
    }
    }

  // launches "child" process with command line parameter
  if(!CreateProcess(NULL,p,NULL,NULL,FALSE,CREATE_SUSPENDED,NULL,NULL,&si,&pi))
    {
      printf( "%s: Error: failed when launching <%s>\n", argv[0], p);
      ErrorReport("CreateProcess");
      return EXIT_FAILURE;
    }
  if(!AssignProcessToJobObject(ghJob,pi.hProcess))
    {ErrorReport("AssignProcessToJobObject");
      return EXIT_FAILURE;
    }

  /* Let's resume the process */
  ResumeThread(pi.hThread);
  // waits and frees handles and malloc
  int w;
    switch (w=WaitForSingleObject(pi.hProcess, INFINITE))
    {
    case WAIT_FAILED:
      printf("Wait failed"); break;
    case WAIT_TIMEOUT:
      printf("Wait timeout"); break;
    case WAIT_OBJECT_0:
      /* Normal case others should not happen. */ break;
    case WAIT_ABANDONED:
      printf("Wait abandonned"); break;
    };

  GetExitCodeProcess(pi.hProcess, (LPDWORD) &ex);

  if (showtime) {
    GetProcessTimes(pi.hProcess, &ft_start, &ft_stop, &ft_system, &ft_user);
    ull_start.LowPart = ft_start.dwLowDateTime;
    ull_start.HighPart = ft_start.dwHighDateTime;
    ull_stop.LowPart = ft_stop.dwLowDateTime;
    ull_stop.HighPart = ft_stop.dwHighDateTime;
    ull_system.LowPart = ft_system.dwLowDateTime;
    ull_system.HighPart = ft_system.dwHighDateTime;
    ull_user.LowPart = ft_user.dwLowDateTime;
    ull_user.HighPart = ft_user.dwHighDateTime;
    cpu_time =
      ((ull_system.QuadPart + ull_user.QuadPart + 0.0) / 10000000.);
    wall_time = (ull_stop.QuadPart - ull_start.QuadPart + 0.0) / 10000000.;
    fprintf(stdout,
	    "why3cpulimit time : %f s\nwhy3cpulimit real time : %f s\n", cpu_time, wall_time);
    fflush(stdout);
  }
  CloseHandle(pi.hProcess);
  CloseHandle(pi.hThread);
  CloseHandle(ghJob);
  free(p);
  if (w == WAIT_TIMEOUT) return 152;
  return ex;
}

#endif /* _WIN32 */

// How to compile under Cygwin (needs make, gcc and win32api):
//                 gcc -Wall -o cpulimit cpulimit.c
