/**************************************************************************/
/*                                                                        */
/*  The Why3 Verification Platform   /   The Why3 Development Team        */
/*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University        */
/*                                                                        */
/*  This software is distributed under the terms of the GNU Lesser        */
/*  General Public License version 2.1, with the special exception        */
/*  on linking described in file LICENSE.                                 */
/*                                                                        */
/**************************************************************************/

#ifndef LOGGING_H
#define LOGGING_H

void init_logging();

void log_msg(char* s, ...) __attribute__ ((format (printf, 1, 2)));
void logging_shutdown(char* s);

#endif
