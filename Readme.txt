The programs use the GMP-library. On Ubuntu this can be installed by

sudo apt-get install libgmp3-dev

Instructions for other operating systems can be found at http://www.mathemagix.org/www/mmdoc/doc/html/external/gmp.en.html

The programs should be compiled with the following flags

g++ Program.cpp -O2 -lgmp -lgmpxx -o ./run