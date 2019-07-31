open Printf

let inverse x =
  let rec loop t t' r r' =
    if r' = 0 then
      if t < 0 then t + 256 else t
    else
      let q = r / r' in
      loop t' (t - q * t') r' (r - q * r')
  in
  loop 0 1 256 x

let () =
  printf "/* binverttab[i] is the multiplicative inverse of 2*i+1 mod 256,\
\n   ie. (binverttab[i] * (2*i+1)) %% 256 == 1 */\n";
  printf "const unsigned char binverttab[128] = {\n";
  for i1 = 0 to 15 do
    printf "  ";
    for i2 = 0 to 7 do
      let i = i1 * 8 + i2 in
      let inv = inverse (2*i+1) in
      assert (((2*i+1) * inv) mod 256 = 1);
      printf "0x%02x," (inverse (2*i+1));
    done;
    printf "\n";
  done;
  printf "};\n%!"
