open Base64

let test t =
  let d = decode (encode t) in
  if d <> t then begin
      Format.eprintf "Failed with %s - %s@." t d; assert false
    end

let tests = [
  "";
  "a";
  "ab";
  "abc";
  "abcd";
  "908ujdas0";
  "(*^HDS)Hl;ady&*(ASD|[]\\a";
  "(*^HDS)Hl;ady&*(ASD|[]\\a'";
  "(*^HDS)Hl;ady&*(ASD|[]\\a'}";
  " dsahn fadslhnoiy90hjnIOG*)YHpn 17uOJASG87oT!@*&%#!ujb c";
  "<L:<A:<adsD:Hp8y2hjp;/\tmsdag8y64830u89(*^T*&(OGdd97s^Ydsa";
  "<L:<A:\n<adsD:Hp8y2hjp;/\tmsdag8y64830u89(*^T*&(OGdd97s^Ydsa";
  "<L:<A:<a\123dsD:Hp8y2hjp;/\tmsda\ng8y648\x1030u89(*^T*&(OGdd97s^Ydsa"
]

let () =
  List.iter test tests;
  Format.printf "all tests passed with success!@."

