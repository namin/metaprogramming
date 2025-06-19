#include <limits.h>
#include <string.h>
#include <string.h>
/*@ predicate submatcher_0(char  * x19) = ((x19[0]=='\0') || (!(x19[0]=='\0') &&
((x19[0]=='a') &&
submatcher_0((x19+1)))));*/
/*@
requires ((strlen(x19)>=0) &&
\valid(x19+(0..strlen(x19))));
assigns \nothing;
ensures \result <==> submatcher_0(x19);
*/
int submatcher_0(char  * x19) {
  char x21 = x19[0];
  int x22 = x21 == '\0';
  int x29;
  if (x22) {
    x29 = 0/*false*/;
  } else {
    int x23 = x21 == 'a';
    int x27;
    if (x23) {
      char  *x24 = x19+1;
      int x25 = submatcher_0(x24);
      x27 = x25;
    } else {
      x27 = 0/*false*/;
    }
    x29 = x27;
  }
  int x30 = x22 || x29;
  return x30;
}
/*@ predicate matcher_star_a(char  * x0) = ((x0[0]=='\0') || (!(x0[0]=='\0') &&
((x0[0]=='a') &&
submatcher_0((x0+1)))));*/
/*@
requires ((strlen(x0)>=0) &&
\valid(x0+(0..strlen(x0))));
assigns \nothing;
ensures \result <==> matcher_star_a(x0);
*/
int matcher_star_a(char  * x0) {
  char x2 = x0[0];
  int x3 = x2 == '\0';
  int x10;
  if (x3) {
    x10 = 0/*false*/;
  } else {
    int x4 = x2 == 'a';
    int x8;
    if (x4) {
      char  *x5 = x0+1;
      int x6 = submatcher_0(x5);
      x8 = x6;
    } else {
      x8 = 0/*false*/;
    }
    x10 = x8;
  }
  int x11 = x3 || x10;
  return x11;
}
