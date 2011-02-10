#!/bin/sed -f

s/theory Why2/&\nuse array.Array as A/;
s/type memory 'a 'z/& = A.t (pointer 'z) 'a/g
s/logic acc (memory 'a1 'a2) (pointer 'a2) : 'a1/logic acc (m:memory 'a1 'a2) (k:pointer 'a2) : 'a1 = A.get m k/
s/logic upd (memory 'a1 'a2) (pointer 'a2) 'a1 : (memory 'a1 'a2)/logic upd (m:memory 'a1 'a2) (k:pointer 'a2) (v:'a1) : (memory 'a1 'a2) = A.set m k v/

/axiom Acc_upd:/,+5 c
/axiom Acc_upd_neq:/,+7 c

# Use polymoprhic map for mono int is silly so comment
#s/  type int_array/& = A.t int int/
#s/  logic access int_array int : int/  logic access (m:int_array) (k:int) : int = A.get m k/
#s/  logic update int_array int int : int_array/  logic update (m:int_array) (k:int) (v:int) : int_array = A.set m k v/

#/axiom Access_update_eq:/,+5 c
#/axiom Access_update_neq:/,+8 c