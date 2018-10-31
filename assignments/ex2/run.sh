cat $1 img.test.c >main.c; cc main.c libpgm.a; ./a.out; open out.pgm
