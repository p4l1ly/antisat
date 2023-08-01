set term png size 400,400
set key off

set output "3v0.png"
set title "3v0"
set xrange [0:15]
set yrange [0:15]
plot "./bench.csv" u 1:4 with points lc rgb "black" pointtype 7 pointsize 1, \
  x with line dt 2 lc rgb "black"

set output "3v1.png"
set title "3v1"
set xrange [0:15]
set yrange [0:15]
plot "./bench.csv" u 1:3 with points lc rgb "black" pointtype 7 pointsize 1, \
  x with line dt 2 lc rgb "black"

set output "3v2.png"
set title "3v2"
set xrange [0:15]
set yrange [0:15]
plot "./bench.csv" u 1:2 with points lc rgb "black" pointtype 7 pointsize 1, \
  x with line dt 2 lc rgb "black"

set output "2v0.png"
set title "2v0"
set xrange [0:15]
set yrange [0:15]
plot "./bench.csv" u 2:4 with points lc rgb "black" pointtype 7 pointsize 1, \
  x with line dt 2 lc rgb "black"

set output "2v1.png"
set title "2v1"
set xrange [0:15]
set yrange [0:15]
plot "./bench.csv" u 2:3 with points lc rgb "black" pointtype 7 pointsize 1, \
  x with line dt 2 lc rgb "black"

set output "1v0.png"
set title "1v0"
set xrange [0:15]
set yrange [0:15]
plot "./bench.csv" u 3:4 with points lc rgb "black" pointtype 7 pointsize 1, \
  x with line dt 2 lc rgb "black"
