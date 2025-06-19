#include <limits.h>
#include <string.h>
#include <string.h>
/*@ predicate submatcher_0(char  * x30) = ((x30[0]=='\0') || ((!(x30[0]=='\0') &&
((x30[0]=='a') &&
\false)) || (!(x30[0]=='\0') &&
((x30[0]=='a') &&
(!((x30+1)[0]=='\0') &&
(((x30+1)[0]=='b') &&
submatcher_0(((x30+1)+1))))))));*/
/*@
requires ((strlen(x30)>=0) &&
\valid(x30+(0..strlen(x30))));
assigns \nothing;
ensures \result <==> submatcher_0(x30);
*/
int submatcher_0(char  * x30) {
  char x32 = x30[0];
  int x33 = x32 == '\0';
  int x50;
  if (x33) {
    x50 = 0/*false*/;
  } else {
    int x34 = x32 == 'a';
    int x48;
    if (x34) {
      char  *x35 = x30+1;
      char x38 = x35[0];
      int x39 = x38 == '\0';
      int x46;
      if (x39) {
        x46 = 0/*false*/;
      } else {
        int x40 = x38 == 'b';
        int x44;
        if (x40) {
          char  *x41 = x35+1;
          int x42 = submatcher_0(x41);
          x44 = x42;
        } else {
          x44 = 0/*false*/;
        }
        x46 = x44;
      }
      x48 = x46;
    } else {
      x48 = 0/*false*/;
    }
    x50 = x48;
  }
  int x37;
  if (x33) {
    x37 = 0/*false*/;
  } else {
    int x34 = x32 == 'a';
    int x36;
    if (x34) {
      x36 = 0/*false*/;
    } else {
      x36 = 0/*false*/;
    }
    x37 = x36;
  }
  int x51 = x37 || x50;
  int x52 = x33 || x51;
  return x52;
}
/*@ predicate matcher_star_ab(char  * x0) = ((x0[0]=='\0') || ((!(x0[0]=='\0') &&
((x0[0]=='a') &&
\false)) || (!(x0[0]=='\0') &&
((x0[0]=='a') &&
(!((x0+1)[0]=='\0') &&
(((x0+1)[0]=='b') &&
submatcher_0(((x0+1)+1))))))));*/
/*@
requires ((strlen(x0)>=0) &&
\valid(x0+(0..strlen(x0))));
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
