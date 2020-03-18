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

#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include "proc.h"
#include "options.h"

// global pointers are initialized with NULL by C semantics
plist processes;

// kill process using os specific routine
void os_kill(pproc p);

void os_kill(pproc p) {
#ifdef _WIN32
  // arbitrarily chosen exit code
  TerminateProcess(p->handle, ERROR_REQUEST_ABORTED);
#else
  kill(p->id, SIGKILL);
#endif
}

void init_process_list () {
  processes = init_list(parallel);
}

void kill_processes(char *id) {
  for (int i = 0; i < processes->len; i++) {
    if (!strcmp(((pproc)(processes->data[i]))->task_id, id)) {
      os_kill((pproc)processes->data[i]);
    }
  }
}

void free_process(pproc proc) {
#ifdef _WIN32
   CloseHandle(proc->handle);
   CloseHandle(proc->job);
#endif
   free(proc->outfile);
   free(proc->task_id);
   free(proc);
}
