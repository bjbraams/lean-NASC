#!/bin/bash
# usage: ocr.sh pdf outdir worker nworkers npages
pdf=$1; out=$2; k=$3; W=$4; n=$5
for ((p=k+1; p<=n; p+=W)); do
  pdftoppm -r 200 -gray -f $p -l $p -singlefile -png "$pdf" "$out/w$k" 2>/dev/null
  tesseract "$out/w$k.png" "$out/t$(printf %04d $p)" >/dev/null 2>&1
done
