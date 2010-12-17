/**************************************************************************/
/*                                                                        */
/*  The Why platform for program certification                            */
/*  Copyright (C) 2002-2008                                               */
/*    Romain BARDOU                                                       */
/*    Jean-François COUCHOT                                               */
/*    Mehdi DOGGUY                                                        */
/*    Jean-Christophe FILLIÂTRE                                           */
/*    Thierry HUBERT                                                      */
/*    Claude MARCHÉ                                                       */
/*    Yannick MOY                                                         */
/*    Christine PAULIN                                                    */
/*    Yann RÉGIS-GIANAS                                                   */
/*    Nicolas ROUSSET                                                     */
/*    Xavier URBAIN                                                       */
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

#include <sys/types.h>
#include <sys/time.h>
#include <time.h>
#include <sys/times.h>
#include <sys/resource.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>
#include <string.h>
#include <sys/wait.h>

int main(int argc, char *argv[]) {
  int timelimit, memlimit;
  struct rlimit res;

  if (argc < 5) {
    fprintf(stderr, "usage: %s <time limit in seconds> \
<virtual memory limit in MiB> <-s|-h> <command>\n\
a null value sets no limit (keeps the actual limit)\n", argv[0]);
    return EXIT_FAILURE;
  }

  /* Fork if requested */
  if(strcmp("-s",argv[3]) == 0){
      int pid = fork ();
      if (pid == -1){
          perror("fork");
          exit(EXIT_FAILURE);
      } else if (pid == 0){
          /* The child continues to execute the program */
      } else {
          /* The parent will not exit this condition */
          int status;
          waitpid(pid, &status, 0);
          struct tms tms;
          times(&tms);
          double time = (double)((tms.tms_cutime + tms.tms_cstime + 0.0)
                                 / sysconf(_SC_CLK_TCK));
          fprintf(stdout, "why3cpulimit time : %f s\n",time);
          if (WIFEXITED(status)){
              return WEXITSTATUS(status);
          }

          kill(getpid(),SIGTERM);
      }
  }

  /* get time limit in seconds from command line */
  timelimit = atoi(argv[1]);

  if (timelimit > 0) {
    /* set the CPU time limit */
    getrlimit(RLIMIT_CPU,&res);
    res.rlim_cur = timelimit;
    setrlimit(RLIMIT_CPU,&res);
  }

  /* get virtual memory limit in MiB from command line */
  memlimit = atol(argv[2]);

  if (memlimit > 0) {
    /* set the CPU time limit */
    getrlimit(RLIMIT_AS,&res);
    res.rlim_cur = memlimit * 1024 * 1024;
    setrlimit(RLIMIT_AS,&res);
  }

  /* execute the command */
  execvp(argv[4],argv+4);
  fprintf(stderr, "%s: exec of '%s' failed (%s)\n",
          argv[0],argv[4],strerror(errno));
  return EXIT_FAILURE;

}

