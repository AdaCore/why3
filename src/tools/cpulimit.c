/**************************************************************************/
/*                                                                        */
/*  The Why platform for program certification                            */
/*  Copyright (C) 2002-2008                                               */
/*    Romain BARDOU                                                       */
/*    Jean-Fran�ois COUCHOT                                               */
/*    Mehdi DOGGUY                                                        */
/*    Jean-Christophe FILLI�TRE                                           */
/*    Thierry HUBERT                                                      */
/*    Claude MARCH�                                                       */
/*    Yannick MOY                                                         */
/*    Christine PAULIN                                                    */
/*    Yann R�GIS-GIANAS                                                   */
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
#include <sys/resource.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>


int main(int argc, char *argv[]) {
  int limit;
  struct rlimit res;

  if (argc < 3) {
    fprintf(stderr,"usage: %s <time limit in seconds> <command>\n",argv[0]);
    return 1;
  }
  /* get time limit in seconds from command line */
  limit = atoi(argv[1]);

  /* set the CPU limit */
  getrlimit(RLIMIT_CPU,&res);
  res.rlim_cur = limit;
  setrlimit(RLIMIT_CPU,&res);
    
  /* exec the command */
  execvp(argv[2],argv+2);
  fprintf(stderr,"%s: %s:command not found",argv[0],argv[2]);
  return errno;
}
