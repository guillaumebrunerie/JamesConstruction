#!/usr/bin/python2

import sys
import re

startblock = re.compile(r"\\>\\AgdaComment{\\{-<(\w+)>-\\}}\\<%")
endblock   = re.compile(r"\\>\\AgdaComment{\\{-</>-\\}}\\<%")

outfile = None
was_new_line = False
was_beginning = False

with open(sys.argv[1]) as infile:
    for line in infile:
        if was_beginning:
            outfile.write("\\\\[-\\baselineskip]\n")
            was_beginning = False
            continue
        if outfile:
            if endblock.match(line):
                outfile.write("\\end{code}\n")
                outfile.close()
                outfile = None
            else:
                if was_new_line:
                    if line == "%\n":
                        outfile.write("\\\\[-0.1cm]\n")
                    else:
                        outfile.write("\\\\\n")
                if line == "\\\\\n":
                    was_new_line = True
                else:
                    outfile.write(line)
                    was_new_line = False
        else:
            res = startblock.match(line)
            if res:
                outfile = open(res.group(1) + ".tex", "w")
                outfile.write("\\begin{code}\n")
                was_beginning = True
                was_new_line = False
