#include <limits.h>
#include <string.h>
/*@ predicate matcher_a_or_b(char  * x0) = ((((x0[0]=='\0')) ? (\false) : (((x0[0]=='a') &&
((x0+1)[0]=='\0')))) || (((x0[0]=='\0')) ? (\false) : (((x0[0]=='b') &&
((x0+1)[0]=='\0')))));*/
/*@
requires ((strlen(x0)>=0) &&
\valid(x0+(0..(strlen(x0)+1)-1)));
assigns \nothing;
ensures \result <==> matcher_a_or_b(x0);
*/
int matcher_a_or_b(char  * x0) {
  char x2 = x0[0];
  int x3 = x2 == '\0';
  int x9;
  if (x3) {
    x9 = 0/*false*/;
  } else {
    int x4 = x2 == 'a';
    int x8;
    if (x4) {
      char  *x5 = x0+1;
      char x6 = x5[0];
      int x7 = x6 == '\0';
      x8 = x7;
    } else {
      x8 = 0/*false*/;
    }
    x9 = x8;
  }
  int x12;
  if (x3) {
    x12 = 0/*false*/;
  } else {
    int x10 = x2 == 'b';
    int x11;
    if (x10) {
      char  *x5 = x0+1;
      char x6 = x5[0];
      int x7 = x6 == '\0';
      x11 = x7;
    } else {
      x11 = 0/*false*/;
    }
    x12 = x11;
  }
  int x13 = x9 || x12;
  return x13;
}
