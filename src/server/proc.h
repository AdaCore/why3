/********************************************************************/
/*                                                                  */
/*  The Why3 Verification Platform   /   The Why3 Development Team  */
/*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  */
/*                                                                  */
/*  This software is distributed under the terms of the GNU Lesser  */
/*  General Public License version 2.1, with the special exception  */
/*  on linking described in file LICENSE.                           */
/*                                                                  */
/********************************************************************/

#ifndef PROC_H
#define PROC_H

#ifdef _WIN32
#include <windows.h>
#else
#include <sys/types.h>
#endif

#include "arraylist.h"

typedef struct {
#ifdef _WIN32
  HANDLE handle;
  HANDLE job;
#else
  pid_t id;
#endif
  int client_key;
  char* task_id;
  char* outfile;
} t_proc, *pproc;

extern plist processes;

// free memory and resources associated with the process p
void free_process(pproc p);

// kill all processes whose client_key is equal to key, and whose task_id is
// equal to id
// if id is NULL, then all processes for this client key are killed
void kill_processes(int key, char *id);

// initialize global list of processes
void init_process_list();

void kill_all_processes();
#endif
