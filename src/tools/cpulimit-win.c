/**************************************************************************/
/*                                                                        */
/*  Copyright (C) 2008-2010                                               */
/*    Dillon PARIENTE 2008                                                */
/*    Claude MARCHE 2010                                                  */
/*                                                                        */
/*  This software is free software; you can redistribute it and/or        */
/*  modify it under the terms of the GNU Library General Public           */
/*  License version 2, with the special exception on linking              */
/*  described in file LICENSE.                                            */
/*                                                                        */
/*  This software is distributed in the hope that it will be useful,      */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  */
/*                                                                        */
/**************************************************************************/

/* $Id: cpulimit-win.c,v 1.3 2009-12-09 08:28:00 nrousset Exp $ */

#include <windows.h>
#include <stdlib.h>
#include <stdio.h>
#include <errno.h>
#include <string.h>

int main(int argc, char *argv[]) {
  STARTUPINFO si;
  PROCESS_INFORMATION pi;
  FILETIME ft_start, ft_stop, ft_system, ft_user;
  ULONGLONG ull_start, ull_stop, ull_system, ull_user;
  double cpu_time, wall_time;
  int i;
  unsigned ex;
  unsigned long s = 0; // length of args after concat
  char * p; // command line parameter
  ZeroMemory(&si, sizeof(si));
  si.cb = sizeof(si);
  ZeroMemory(&pi, sizeof(pi));

  showtime = argc >= 4 && !strncmp("-s",argv[3],3);
  hidetime = argc >= 4 && !strncmp("-h",argv[3],3);

  if (argc < 5 || !(showtime || hidetime)) {
    fprintf(stderr, "usage: %s <time limit in seconds> <virtual memory limit in MiB>\n"
                    "          <show/hide cpu time: -s|-h> <command> <args>...\n\n"
                    "Zero sets no limit (keeps the actual limit)\n", argv[0]);
    return EXIT_FAILURE;
  }

  // concats argv[4..] into a single command line parameter
  for (i = 4; i < argc; i++)
    s += strlen(argv[i]) + 1;
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
    strncat(p, argv[i], strlen(argv[i]));
    if (i < argc - 1) strcat(p, " ");
  }
  // launches "child" process with command line parameter
  if (!CreateProcess(NULL, p, NULL, NULL, FALSE, 0, NULL, NULL, &si, &pi)) {
    printf( "%s: Error: failed when launching <%s>\n", argv[0], p);
    return EXIT_FAILURE;
  }
  // waits, terminates and frees handles and malloc
  int w = WaitForSingleObject(pi.hProcess, 1000 * atoi(argv[1]));
  TerminateProcess(pi.hProcess, 10);
  GetExitCodeProcess(pi.hProcess, (LPDWORD) &ex);
  if (showtime) {
    GetProcessTimes(pi.hProcess, &ft_start, &ft_stop, &ft_system, &ft_user);
    ull_start = (((ULONGLONG) ft_start.dwHighDateTime) << 32) + ft_start.dwLowDateTime;
    ull_stop = (((ULONGLONG) ft_stop.dwHighDateTime) << 32) + ft_stop.dwLowDateTime;
    ull_system = (((ULONGLONG) ft_system.dwHighDateTime) << 32) + ft_system.dwLowDateTime;
    ull_user = (((ULONGLONG) ft_user.dwHighDateTime) << 32) + ft_user.dwLowDateTime;
    cpu_time = (double)((ull_system + ull_user + 0.0) / 10000000U);
    wall_time = (double)((ull_stop - ull_start + 0.0) / 10000000U);
    fprintf(stdout, "why3cpulimit time : %f s\n", cpu_time);
  }
  CloseHandle(pi.hProcess);
  CloseHandle(pi.hThread);
  free(p);
  if (w == WAIT_TIMEOUT) return 152;
  return ex;
}

// How to compile under Cygwin (needs make, gcc and win32api):
//                 gcc -Wall -o cpulimit cpulimit.c
