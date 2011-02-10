#!/bin/sed -f

s/theory Why2/&\nuse array.Array as A/;
s/type memory 't 'v/& = A.t (pointer 't) 'v/g
s/logic select (memory 'a2 'a1) (pointer 'a2) : 'a1/logic select (m:memory 'a1 'a2) (k:pointer 'a1) : 'a2 = A.get m k/
s/logic store (memory 'a1 'a2) (pointer 'a1) 'a2 : (memory 'a1 'a2)/logic store (m:memory 'a1 'a2) (k:pointer 'a1) (v:'a2) : (memory 'a1 'a2) = A.set m k v/

/axiom Select_store_eq:/,+7 c
/axiom Select_store_neq:/,+7 c

# Use polymoprhic map for mono int is silly so comment
#s/  type int_array/& = A.t int int/
#s/  logic access int_array int : int/  logic access (m:int_array) (k:int) : int = A.get m k/
#s/  logic update int_array int int : int_array/  logic update (m:int_array) (k:int) (v:int) : int_array = A.set m k v/

#/axiom Access_update_eq:/,+5 c
#/axiom Access_update_neq:/,+8 c