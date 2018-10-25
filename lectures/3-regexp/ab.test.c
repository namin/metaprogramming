#include <stdio.h>

int main(void) {
  printf("1 == %d\n", matcher_ab("ab"));
  printf("0 == %d\n", matcher_ab("abc"));
  printf("0 == %d\n", matcher_ab("cab"));
  printf("0 == %d\n", matcher_ab("ac"));
  return 0;
}
