cat $1 img.test.c >main.c; cc -lm main.c libpgm.a; ./a.out; display out.pgm
