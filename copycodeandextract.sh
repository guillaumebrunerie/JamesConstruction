#!/bin/bash

ORIG_DIR="$PWD"

# Where the Agda files are
AGDA_PATH="$PWD"

# Where should the LaTeX files be put (must be a different directory, will be erased!)
LATEX_PATH="$PWD"/../code

# List of the files to be extracted (including their dependencies)
files="Base Pushout PathInduction ExPathInduction PathInductionSimplified JamesTwoMaps"

mkdir -p "$LATEX_PATH"
rm -rf "$LATEX_PATH"/*


echo "=== Copying the files ==="

cd "$AGDA_PATH"
for i in $files
do
    newname="$LATEX_PATH/${i}.lagda"
    echo "\\begin{code}" >> "$newname"
    cat "${i}.agda" >> "$newname"
    echo "\\end{code}" >> "$newname"
done


echo "=== Compiling ==="

cd "$LATEX_PATH"
for i in $files
do
    agda --latex "${i}.lagda"
done


echo "=== Extracting ==="

for i in $files
do
    "$ORIG_DIR"/extract.py "latex/${i}.tex"
done


echo "=== Done ==="
