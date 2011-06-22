val t_dist : term -> term -> float
  (** returns an heuristic distance between the two given terms. The
      result is always between 0.0 and 1.0. It is guaranteed that if
      the result is 0.0 then the terms are equal modulo alpha *)
