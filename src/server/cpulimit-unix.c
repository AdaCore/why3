/********************************************************************/
/*                                                                  */
/*  The Why3 Verification Platform   /   The Why3 Development Team  */
/*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  */
/*                                                                  */
/*  This software is distributed under the terms of the GNU Lesser  */
/*  General Public License version 2.1, with the special exception  */
/*  on linking described in file LICENSE.                           */
/*                                                                  */
/********************************************************************/

#ifndef _WIN32

#include <sys/types.h>
#include <sys/time.h>
#include <time.h>
#include <sys/times.h>
#include <sys/resource.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <signal.h>
#include <errno.h>
#include <string.h>
#include <sys/wait.h>

static int wallclock_timelimit = 60;
static int showtime = 0, hidetime = 0;

void show_time() {
  struct tms tms;
  double time;
  if (showtime) {
    times(&tms);
    time = (double)((tms.tms_cutime + tms.tms_cstime + 0.0)
                    / sysconf(_SC_CLK_TCK));
    fprintf(stderr, "why3cpulimit time : %f s\n", time);
  }
}

void wallclock_timelimit_reached() {
  fprintf(stderr,
          "Why3cpulimit: wallclock timelimit %d reached, killing command\n",
          wallclock_timelimit);
}


void usage(char *argv0) {
  fprintf(stderr,
          "usage: %s <time limit in seconds> <virtual memory limit in MiB>\n"
          "          <show/hide cpu time: -s|-h> <command> <args>...\n\n"
          "Zero sets no limit (keeps the actual limit)\n", argv0);
  exit(EXIT_FAILURE);
}

int main(int argc, char *argv[]) {
  long timelimit, memlimit;
  struct rlimit res;

  if (argc < 5) usage(argv[0]);

  showtime = !strcmp("-s", argv[3]);
  hidetime = !strcmp("-h", argv[3]);

  if (!(showtime || hidetime)) usage(argv[0]);

  /* get time limit in seconds from command line */
  timelimit = atol(argv[1]);
  if (timelimit < 0) usage(argv[0]);

  /* get virtual memory limit in MiB from command line */
  memlimit = atol(argv[2]);
  if (memlimit < 0) usage(argv[0]);

  /* Fork if requested */
  if (showtime || timelimit) {
    pid_t pid = fork ();

    if (pid == -1) {
      perror("fork");
      exit(EXIT_FAILURE);
    }

    if (pid > 0) {
      int status;
      pid_t p;

      if (timelimit) {
        /* set a wallclock time limit as last resort */
        struct sigaction sa;
        sa.sa_handler = &wallclock_timelimit_reached;
        sigemptyset(&sa.sa_mask);
        sa.sa_flags = 0;
        sigaction(SIGALRM, &sa, NULL);
        wallclock_timelimit = 2*timelimit + 60;
        alarm(wallclock_timelimit);
      }

      /* wait for the subprocess */
      p = waitpid(pid, &status, 0);

      if (p <= 0) {
        kill(pid, SIGKILL);
        p = waitpid(pid, &status, 0);
        if (p <= 0) {
          perror("why3cpulimit waitpid");
          kill(getpid(), SIGTERM);
        }
      }

      show_time();

      if (WIFEXITED(status)) return WEXITSTATUS(status);
      if (WIFSIGNALED(status)) kill(getpid(), WTERMSIG(status));

      fprintf(stderr, "why3cpulimit: child exited neither normally nor because of a signal\n");
      kill(getpid(), SIGTERM);
    }
  }

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

  /* execute the command */
  execvp(argv[4],argv+4);
  fprintf(stderr, "%s: exec of '%s' failed (%s)\n",
          argv[0],argv[4],strerror(errno));

  return EXIT_FAILURE;

}

#endif /* _WIN32 */
