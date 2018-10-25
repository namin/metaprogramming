#include <limits.h>
#include <string.h>
/*@ predicate matcher_ab(char  * x0) = ((((x0[0]=='\0')) ? (\false) : (((x0[0]=='a') &&
\false))) || (((x0[0]=='\0')) ? (\false) : (((x0[0]=='a') &&
((((x0+1)[0]=='\0')) ? (\false) : ((((x0+1)[0]=='b') &&
(((x0+1)+1)[0]=='\0'))))))));*/
/*@
requires ((strlen(x0)>=0) &&
\valid(x0+(0..(strlen(x0)+1)-1)));
assigns \nothing;
ensures \result <==> matcher_ab(x0);
*/
int matcher_ab(char  * x0) {
  char x2 = x0[0];
  int x3 = x2 == '\0';
  int x7;
  if (x3) {
    x7 = 0/*false*/;
  } else {
    int x4 = x2 == 'a';
    int x6;
    if (x4) {
      x6 = 0/*false*/;
    } else {
      x6 = 0/*false*/;
    }
    x7 = x6;
  }
  int x17;
  if (x3) {
    x17 = 0/*false*/;
  } else {
    int x4 = x2 == 'a';
    int x16;
    if (x4) {
      char  *x5 = x0+1;
      char x8 = x5[0];
      int x9 = x8 == '\0';
      int x15;
      if (x9) {
        x15 = 0/*false*/;
      } else {
        int x10 = x8 == 'b';
        int x14;
        if (x10) {
          char  *x11 = x5+1;
          char x12 = x11[0];
          int x13 = x12 == '\0';
          x14 = x13;
        } else {
          x14 = 0/*false*/;
        }
        x15 = x14;
      }
      x16 = x15;
    } else {
      x16 = 0/*false*/;
    }
    x17 = x16;
  }
  int x18 = x7 || x17;
  return x18;
}
