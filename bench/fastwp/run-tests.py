#!/usr/bin/env python

import glob
import os.path
import tools

# list_of_files = glob.glob ("*.mlw")
list_of_files = [
   "try.mlw",
   "assign.mlw",
   "app.mlw",
   "call.mlw",
   "result.mlw",
   "call_exc.mlw",
   "if.mlw",
   "assert.mlw",
   "raise.mlw",
   "abstract.mlw"
   ]

def compute_expected_output(fn, outputfile):
    test = open(fn, "r")
    inp = test.readlines()
    output = tools.grep ("\(\* (\w*) \*\)", inp)
    tools.save_to_file (outputfile, output)

def main():
    for fn in list_of_files:
        basename = os.path.splitext(fn)
        basename = basename[0]
        xoutfile = basename + ".actout"
        exp_output = basename + ".out"
        output = tools.run_why (fn)
        pattern = fn + ".*: (.+) \(.*\)"
        output = tools.grep (pattern, output)
        tools.save_to_file (xoutfile, output)
        compute_expected_output(fn, exp_output)
        if tools.diff (exp_output, xoutfile) == 0:
            print fn, " : OK"
        else:
            print fn, " : DIFF"
        os.remove (xoutfile)
        os.remove (exp_output)

if __name__ == "__main__":
    main()
