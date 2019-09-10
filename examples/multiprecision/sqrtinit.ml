open Printf

let () =
  printf "/* The common 0x100 was removed */\
    \nstatic const unsigned char invsqrttab[384] = {\n";
  for i1 = 16 to 63 do
    printf "  ";
    for i2 = 0 to 7 do
      let i = i1 * 8 + i2 in
      let j = int_of_float (sqrt (512. /. (float_of_int i +. 0.5)) *. 256. +. 0.5) in
      printf "0x%02x," (j - 256);
    done;
    printf " /* sqrt(1/%x)..sqrt(1/%x) */\n" (i1*8) (i1*8+7);
  done;
  printf "};\n%!"
