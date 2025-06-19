#include <limits.h>
#include <string.h>
#include <string.h>
/*@ predicate submatcher_0(char  * x42) = ((x42[0]=='\0') || (((!(x42[0]=='\0') &&
((x42[0]=='a') &&
\false)) || (!(x42[0]=='\0') &&
((x42[0]=='a') &&
(!((x42+1)[0]=='\0') &&
(((x42+1)[0]=='b') &&
submatcher_0(((x42+1)+1))))))) || ((!(x42[0]=='\0') &&
((x42[0]=='a') &&
\false)) || (!(x42[0]=='\0') &&
((x42[0]=='a') &&
(!((x42+1)[0]=='\0') &&
(((x42+1)[0]=='c') &&
submatcher_0(((x42+1)+1)))))))));*/
/*@
requires ((strlen(x42)>=0) &&
\valid(x42+(0..strlen(x42))));
assigns \nothing;
ensures \result <==> submatcher_0(x42);
*/
int submatcher_0(char  * x42) {
  char x44 = x42[0];
  int x45 = x44 == '\0';
  int x62;
  if (x45) {
    x62 = 0/*false*/;
  } else {
    int x46 = x44 == 'a';
    int x60;
    if (x46) {
      char  *x47 = x42+1;
      char x50 = x47[0];
      int x51 = x50 == '\0';
      int x58;
      if (x51) {
        x58 = 0/*false*/;
      } else {
        int x52 = x50 == 'b';
        int x56;
        if (x52) {
          char  *x53 = x47+1;
          int x54 = submatcher_0(x53);
          x56 = x54;
        } else {
          x56 = 0/*false*/;
        }
        x58 = x56;
      }
      x60 = x58;
    } else {
      x60 = 0/*false*/;
    }
    x62 = x60;
  }
  int x73;
  if (x45) {
    x73 = 0/*false*/;
  } else {
    int x46 = x44 == 'a';
    int x71;
    if (x46) {
      char  *x47 = x42+1;
      char x50 = x47[0];
      int x51 = x50 == '\0';
      int x69;
      if (x51) {
        x69 = 0/*false*/;
      } else {
        int x64 = x50 == 'c';
        int x67;
        if (x64) {
          char  *x53 = x47+1;
          int x65 = submatcher_0(x53);
          x67 = x65;
        } else {
          x67 = 0/*false*/;
        }
        x69 = x67;
      }
      x71 = x69;
    } else {
      x71 = 0/*false*/;
    }
    x73 = x71;
  }
  int x49;
  if (x45) {
    x49 = 0/*false*/;
  } else {
    int x46 = x44 == 'a';
    int x48;
    if (x46) {
      x48 = 0/*false*/;
    } else {
      x48 = 0/*false*/;
    }
    x49 = x48;
  }
  int x63 = x49 || x62;
  int x74 = x49 || x73;
  int x75 = x63 || x74;
  int x76 = x45 || x75;
  return x76;
}
/*@ predicate matcher_star_ab_or_ac(char  * x0) = ((x0[0]=='\0') || (((!(x0[0]=='\0') &&
((x0[0]=='a') &&
\false)) || (!(x0[0]=='\0') &&
((x0[0]=='a') &&
(!((x0+1)[0]=='\0') &&
(((x0+1)[0]=='b') &&
submatcher_0(((x0+1)+1))))))) || ((!(x0[0]=='\0') &&
((x0[0]=='a') &&
\false)) || (!(x0[0]=='\0') &&
((x0[0]=='a') &&
(!((x0+1)[0]=='\0') &&
(((x0+1)[0]=='c') &&
submatcher_0(((x0+1)+1)))))))));*/
/*@
requires ((strlen(x0)>=0) &&
\valid(x0+(0..strlen(x0))));
assigns \nothing;
ensures \result <==> matcher_star_ab_or_ac(x0);
*/
int matcher_star_ab_or_ac(char  * x0) {
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
  int x31;
  if (x3) {
    x31 = 0/*false*/;
  } else {
    int x4 = x2 == 'a';
    int x29;
    if (x4) {
      char  *x5 = x0+1;
      char x8 = x5[0];
      int x9 = x8 == '\0';
      int x27;
      if (x9) {
        x27 = 0/*false*/;
      } else {
        int x22 = x8 == 'c';
        int x25;
        if (x22) {
          char  *x11 = x5+1;
          int x23 = submatcher_0(x11);
          x25 = x23;
        } else {
          x25 = 0/*false*/;
        }
        x27 = x25;
      }
      x29 = x27;
    } else {
      x29 = 0/*false*/;
    }
    x31 = x29;
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
  int x32 = x7 || x31;
  int x33 = x21 || x32;
  int x34 = x3 || x33;
  return x34;
}
