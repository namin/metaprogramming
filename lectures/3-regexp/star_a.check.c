#include <limits.h>
#include <string.h>
/*@ predicate submatcher_0(char  * x22) = ((x22[0]=='\0') || (((x22[0]=='\0')) ? (\false) : (((x22[0]=='a') &&
submatcher_0((x22+1))))));*/
/*@
requires ((strlen(x22)>=0) &&
\valid(x22+(0..(strlen(x22)+1)-1)));
assigns \nothing;
ensures \result <==> submatcher_0(x22);
*/
int submatcher_0(char  * x22) {
  char x24 = x22[0];
  int x25 = x24 == '\0';
  int x32;
  if (x25) {
    x32 = 0/*false*/;
  } else {
    int x26 = x24 == 'a';
    int x30;
    if (x26) {
      char  *x27 = x22+1;
      int x28 = submatcher_0(x27);
      x30 = x28;
    } else {
      x30 = 0/*false*/;
    }
    x32 = x30;
  }
  int x33 = x25 || x32;
  return x33;
}
/*@ predicate matcher_star_a(char  * x0) = ((x0[0]=='\0') || (((x0[0]=='\0')) ? (\false) : (((x0[0]=='a') &&
submatcher_0((x0+1))))));*/
/*@
requires ((strlen(x0)>=0) &&
\valid(x0+(0..(strlen(x0)+1)-1)));
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
