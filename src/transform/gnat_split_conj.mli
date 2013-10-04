val split_conj_name : string
(* This transformation splits conjunctions, cases, if-then-else and
   equivalences, and nothing else. Also, it does it only on the
   "right-hand-side" of a goal, never in the context. *)
