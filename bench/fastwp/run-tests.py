#!/usr/bin/env python

import glob
import os.path
import tools

def main():
    # list_of_files = glob.glob ("*.mlw")
    list_of_files = [ "assign.mlw" ]
    for fn in list_of_files:
        basename = os.path.splitext(fn)
        basename = basename[0]
        output = tools.run_why (fn)
        pattern = fn + ".*: (.+) \(.*\)"
        output = tools.grep (pattern, output)
        xoutfile = basename + ".xout"
        tools.save_to_file (xoutfile, output)
        exp_output_file = basename + ".out"
        if tools.diff (xoutfile, exp_output_file) == 0:
            print fn, " : OK"
        else:
            print fn, " : DIFF"
        os.remove (xoutfile)

if __name__ == "__main__":
    main()
