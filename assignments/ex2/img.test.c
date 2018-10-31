#include "pgma_io.h"

int main(void) {
  int w, h, m;
  int* ps;
  pgma_read("takaosan.pgm", &w, &h, &m, &ps);
  p(w, h, ps);

  // Hack to calibrate the min and max,
  // to avoid (obvious) discrepancy between JPG and PGM.
  ps[0] = 0;
  ps[1] = 255;

  pgma_write("out.pgm", w, h, ps);
  return 0;
}
