#include <limits.h>
#include <string.h>
/*@ predicate submatcher_0(char  * x45) = ((x45[0]=='\0') || (((((x45[0]=='\0')) ? (\false) : (((x45[0]=='a') &&
\false))) || (((x45[0]=='\0')) ? (\false) : (((x45[0]=='a') &&
((((x45+1)[0]=='\0')) ? (\false) : ((((x45+1)[0]=='b') &&
submatcher_0(((x45+1)+1))))))))) || ((((x45[0]=='\0')) ? (\false) : (((x45[0]=='a') &&
\false))) || (((x45[0]=='\0')) ? (\false) : (((x45[0]=='a') &&
((((x45+1)[0]=='\0')) ? (\false) : ((((x45+1)[0]=='c') &&
submatcher_0(((x45+1)+1)))))))))));*/
/*@
requires ((strlen(x45)>=0) &&
\valid(x45+(0..(strlen(x45)+1)-1)));
assigns \nothing;
ensures \result <==> submatcher_0(x45);
*/
int submatcher_0(char  * x45) {
  char x47 = x45[0];
  int x48 = x47 == '\0';
  int x65;
  if (x48) {
    x65 = 0/*false*/;
  } else {
    int x49 = x47 == 'a';
    int x63;
    if (x49) {
      char  *x50 = x45+1;
      char x53 = x50[0];
      int x54 = x53 == '\0';
      int x61;
      if (x54) {
        x61 = 0/*false*/;
      } else {
        int x55 = x53 == 'b';
        int x59;
        if (x55) {
          char  *x56 = x50+1;
          int x57 = submatcher_0(x56);
          x59 = x57;
        } else {
          x59 = 0/*false*/;
        }
        x61 = x59;
      }
      x63 = x61;
    } else {
      x63 = 0/*false*/;
    }
    x65 = x63;
  }
  int x76;
  if (x48) {
    x76 = 0/*false*/;
  } else {
    int x49 = x47 == 'a';
    int x74;
    if (x49) {
      char  *x50 = x45+1;
      char x53 = x50[0];
      int x54 = x53 == '\0';
      int x72;
      if (x54) {
        x72 = 0/*false*/;
      } else {
        int x67 = x53 == 'c';
        int x70;
        if (x67) {
          char  *x56 = x50+1;
          int x68 = submatcher_0(x56);
          x70 = x68;
        } else {
          x70 = 0/*false*/;
        }
        x72 = x70;
      }
      x74 = x72;
    } else {
      x74 = 0/*false*/;
    }
    x76 = x74;
  }
  int x52;
  if (x48) {
    x52 = 0/*false*/;
  } else {
    int x49 = x47 == 'a';
    int x51;
    if (x49) {
      x51 = 0/*false*/;
    } else {
      x51 = 0/*false*/;
    }
    x52 = x51;
  }
  int x66 = x52 || x65;
  int x77 = x52 || x76;
  int x78 = x66 || x77;
  int x79 = x48 || x78;
  return x79;
}
/*@ predicate matcher_star_ab_or_ac(char  * x0) = ((x0[0]=='\0') || (((((x0[0]=='\0')) ? (\false) : (((x0[0]=='a') &&
\false))) || (((x0[0]=='\0')) ? (\false) : (((x0[0]=='a') &&
((((x0+1)[0]=='\0')) ? (\false) : ((((x0+1)[0]=='b') &&
submatcher_0(((x0+1)+1))))))))) || ((((x0[0]=='\0')) ? (\false) : (((x0[0]=='a') &&
\false))) || (((x0[0]=='\0')) ? (\false) : (((x0[0]=='a') &&
((((x0+1)[0]=='\0')) ? (\false) : ((((x0+1)[0]=='c') &&
submatcher_0(((x0+1)+1)))))))))));*/
/*@
requires ((strlen(x0)>=0) &&
\valid(x0+(0..(strlen(x0)+1)-1)));
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
