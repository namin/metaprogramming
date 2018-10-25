#include <limits.h>
#include <string.h>
/*@ predicate submatcher_0(char  * x33) = ((x33[0]=='\0') || ((((x33[0]=='\0')) ? (\false) : (((x33[0]=='a') &&
\false))) || (((x33[0]=='\0')) ? (\false) : (((x33[0]=='a') &&
((((x33+1)[0]=='\0')) ? (\false) : ((((x33+1)[0]=='b') &&
submatcher_0(((x33+1)+1))))))))));*/
/*@
requires ((strlen(x33)>=0) &&
\valid(x33+(0..(strlen(x33)+1)-1)));
assigns \nothing;
ensures \result <==> submatcher_0(x33);
*/
int submatcher_0(char  * x33) {
  char x35 = x33[0];
  int x36 = x35 == '\0';
  int x53;
  if (x36) {
    x53 = 0/*false*/;
  } else {
    int x37 = x35 == 'a';
    int x51;
    if (x37) {
      char  *x38 = x33+1;
      char x41 = x38[0];
      int x42 = x41 == '\0';
      int x49;
      if (x42) {
        x49 = 0/*false*/;
      } else {
        int x43 = x41 == 'b';
        int x47;
        if (x43) {
          char  *x44 = x38+1;
          int x45 = submatcher_0(x44);
          x47 = x45;
        } else {
          x47 = 0/*false*/;
        }
        x49 = x47;
      }
      x51 = x49;
    } else {
      x51 = 0/*false*/;
    }
    x53 = x51;
  }
  int x40;
  if (x36) {
    x40 = 0/*false*/;
  } else {
    int x37 = x35 == 'a';
    int x39;
    if (x37) {
      x39 = 0/*false*/;
    } else {
      x39 = 0/*false*/;
    }
    x40 = x39;
  }
  int x54 = x40 || x53;
  int x55 = x36 || x54;
  return x55;
}
/*@ predicate matcher_star_ab(char  * x0) = ((x0[0]=='\0') || ((((x0[0]=='\0')) ? (\false) : (((x0[0]=='a') &&
\false))) || (((x0[0]=='\0')) ? (\false) : (((x0[0]=='a') &&
((((x0+1)[0]=='\0')) ? (\false) : ((((x0+1)[0]=='b') &&
submatcher_0(((x0+1)+1))))))))));*/
/*@
requires ((strlen(x0)>=0) &&
\valid(x0+(0..(strlen(x0)+1)-1)));
assigns \nothing;
ensures \result <==> matcher_star_ab(x0);
*/
int matcher_star_ab(char  * x0) {
  char x2 = x0[0];
  int x3 = x2 == '\0';
  int x20;
  if (x3) {
    x20 = 0/*false*/;
  } else {
    int x4 = x2 == 'a';
    int x18;
    if (x4) {
      char  *x5 = x0+1;
      char x8 = x5[0];
      int x9 = x8 == '\0';
      int x16;
      if (x9) {
        x16 = 0/*false*/;
      } else {
        int x10 = x8 == 'b';
        int x14;
        if (x10) {
          char  *x11 = x5+1;
          int x12 = submatcher_0(x11);
          x14 = x12;
        } else {
          x14 = 0/*false*/;
        }
        x16 = x14;
      }
      x18 = x16;
    } else {
      x18 = 0/*false*/;
    }
    x20 = x18;
  }
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
  int x21 = x7 || x20;
  int x22 = x3 || x21;
  return x22;
}
