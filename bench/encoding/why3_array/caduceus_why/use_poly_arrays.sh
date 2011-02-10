#!/bin/sed -f

s/theory Why2/&\nuse array.Array as A/;
s/type farray 'a/& = A.t int 'a/
s/logic access (farray 'a1) int : 'a1/logic access (m:farray 'a1) (k:int) : 'a1 = A.get m k/
s/logic update (farray 'a1) int 'a1 : (farray 'a1)/logic update (m:farray 'a1) (k:int) (v:'a1) : (farray 'a1) = A.set m k v/

/axiom Access_update:/,+4 c
/axiom Access_update_neq:/,+7 c
