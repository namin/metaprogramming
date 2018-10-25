#include <stdio.h>

int main(void) {
  printf("1 == %d\n", matcher_star_ab_or_ac("ab"));
  printf("1 == %d\n", matcher_star_ab_or_ac("ac"));
  printf("1 == %d\n", matcher_star_ab_or_ac("acac"));
  printf("1 == %d\n", matcher_star_ab_or_ac("acab"));
  printf("0 == %d\n", matcher_star_ab_or_ac("abc"));
  printf("0 == %d\n", matcher_star_ab_or_ac("cab"));
  printf("0 == %d\n", matcher_star_ab_or_ac("abca"));
  printf("0 == %d\n", matcher_star_ab_or_ac("caba"));
  printf("0 == %d\n", matcher_star_ab_or_ac("ad"));
  return 0;
}
