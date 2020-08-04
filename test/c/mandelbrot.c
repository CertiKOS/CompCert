/* The Computer Language Shootout
   http://shootout.alioth.debian.org/

   contributed by Greg Buchholz

   for the debian (AMD) machine...
   compile flags:  -O3 -ffast-math -march=athlon-xp -funroll-loops

   for the gp4 (Intel) machine...
   compile flags:  -O3 -ffast-math -march=pentium4 -funroll-loops
*/

#include <stdio.h>
#include <stdlib.h>

int MAN_GLB_INT1 = 1;
double MAN_GLB_DB_ZERO = 0.0;

double MAN_GLB_DB_2 = 2.0;

double MAN_GLB_DB_1 = 1.0;

double MAN_GLB_DB_HALF = 1.5;

int main (int argc, char **argv)
{
    int w, h, bit_num = 0;
    char byte_acc = 0;
    int i, iter = 50;
    double x, y, limit = MAN_GLB_DB_2;
    double Zr, Zi, Cr, Ci, Tr, Ti;

    if (argc < 2) {
      w = h = 3000;
    } else {
      w = h = atoi(argv[MAN_GLB_INT1]);
    }

    printf("P4\n%d %d\n",w,h);

    for(y=0;y<h;y=y+MAN_GLB_INT1)
    {
        for(x=0;x<w;x=x+MAN_GLB_INT1)
        {
            Zr = Zi = Tr = Ti = MAN_GLB_DB_ZERO;
            Cr = (MAN_GLB_DB_2 * x / w - MAN_GLB_DB_HALF); Ci=(MAN_GLB_DB_2 * y / h - MAN_GLB_DB_1);

            for (i=0;i<iter && (Tr+Ti <= limit*limit);++i)
            {
                Zi = MAN_GLB_DB_2 * Zr * Zi + Ci;
                Zr = Tr - Ti + Cr;
                Tr = Zr * Zr;
                Ti = Zi * Zi;
            }

            byte_acc <<= MAN_GLB_INT1;
            if(Tr+Ti <= limit*limit) byte_acc |= 0x01;

            ++bit_num;

            if(bit_num == 8)
            {
                putc(byte_acc,stdout);
                byte_acc = 0;
                bit_num = 0;
            }
            else if(x == w - MAN_GLB_INT1)
            {
                byte_acc <<= (8-w%8);
                putc(byte_acc,stdout);
                byte_acc = 0;
                bit_num = 0;
            }
        }
    }
    return 0;
}

/***********
 build & benchmark results

BUILD COMMANDS FOR: mandelbrot.gcc-2.gcc

Fri Sep 15 03:05:43 PDT 2006

/usr/bin/gcc -pipe -Wall -O3 -fomit-frame-pointer -funroll-loops -march=pentium4 -D_ISOC9X_SOURCE -mfpmath=sse -msse2 -lm mandelbrot.gcc-2.c -o mandelbrot.gcc-2.gcc_run
mandelbrot.gcc-2.c: In function 'main':
mandelbrot.gcc-2.c:23: warning: implicit declaration of function 'atoi'
mandelbrot.gcc-2.c:62: warning: control reaches end of non-void function

=================================================================
COMMAND LINE (%A is single numeric argument):

mandelbrot.gcc-2.gcc_run %A
N=3000

PROGRAM OUTPUT
==============
P4
3000 3000
****************/
