#!/usr/bin/env python

import tools
import sys

def main():
    args = [ "--debug" , "print_labels"]
    tools.print_list (tools.run_why (sys.argv[1], args))


if __name__ == "__main__":
    main()
