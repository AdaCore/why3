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

#include <caml/mlvalues.h>
#include <caml/memory.h>

/* Whenever this variable reaches 1, a garbage collection starts and the
   variable is reset to 0. Unfortunately, it might take as few as 50
   allocations of Glib/Gdk/Gtk objects for the variable to go from 0 to 1.
   Most IDE operations involve tens, if not, hundreds, of such objects,
   thus causing the garbage collector to constantly run. */
extern double caml_extra_heap_resources;

/* Set the accumulator to -inf to prevent it from reaching 1. It might
   still reach it, since any collection sets it to 0, so the hack only
   works for a short while. */
CAMLprim value ml_reset_gc(value unit)
{
  CAMLparam1(unit);
  caml_extra_heap_resources = - 1.0 / 0.0;
  CAMLreturn(Val_unit);
}
