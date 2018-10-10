| ?-
ty([], lam(x, var(x)), T).
ty([], lam(x, var(x)), T).

T = arr(A,A) ? a
a

no

| ?-
solve0(ty([], lam(x, var(x)), T), P, Ok).
solve0(ty([], lam(x, var(x)), T), P, Ok).

Ok = true
P = (ty([],lam(x,var(x)),arr(A,A)):-(add([],(x,A),[(x,A)]):-builtin),(ty([(x,A)],var(x),A):-(in((x,A),[(x,A)]):-builtin)))
T = arr(A,A)

yes

| ?-
ty([], lam(x,lam(y,var(x))), T).
ty([], lam(x,lam(y,var(x))), T).

T = arr(A,arr(_,A)) ? a
a

no

| ?-

solve0(ty([], lam(x,lam(y,var(x))), T), P, Ok).

Ok = true
P = (ty([],lam(x,lam(y,var(x))),arr(A,arr(B,A))):-(add([],(x,A),[(x,A)]):-builtin),(ty([(x,A)],lam(y,var(x)),arr(B,A)):-(add([(x,A)],(y,B),[(y,B),(x,A)]):-builtin),(ty([(y,B),(x,A)],var(x),A):-(in((x,A),[(y,B),(x,A)]):-builtin))))
T = arr(A,arr(B,A))

yes

| ?-
ty([], lam(x,lam(x,var(x))), T).
ty([], lam(x,lam(x,var(x))), T).

T = arr(_,arr(A,A)) ? a
a

no

| ?-
solve0(ty([], lam(x,lam(x,var(x))), T), P, Ok).
solve0(ty([], lam(x,lam(x,var(x))), T), P, Ok).

Ok = true
P = (ty([],lam(x,lam(x,var(x))),arr(A,arr(B,B))):-(add([],(x,A),[(x,A)]):-builtin),(ty([(x,A)],lam(x,var(x)),arr(B,B)):-(add([(x,A)],(x,B),[(x,B),(x,A)]):-builtin),(ty([(x,B),(x,A)],var(x),B):-(in((x,B),[(x,B),(x,A)]):-builtin))))
T = arr(A,arr(B,B))

yes

| ?- ty([], lam(x,app(var(x),var(x))), T).
ty([], lam(x,app(var(x),var(x))), T).

cannot display cyclic term for T ? a
a

| ?-
tyc([], lam(x,app(var(x),var(x))), T).
tyc([], lam(x,app(var(x),var(x))), T).

no

| ?- solve0(ty([], lam(x,app(var(x),var(x))), T), P, Ok).
solve0(ty([], lam(x,app(var(x),var(x))), T), P, Ok).

Ok = true
cannot display cyclic term for P
cannot display cyclic term for T

yes

| ?- solve0(tyc([], lam(x,app(var(x),var(x))), T), P, Ok).
solve0(tyc([], lam(x,app(var(x),var(x))), T), P, Ok).

Ok = false
P = (tyc([],lam(x,app(var(x),var(x))),arr(arr(A,B),B)):-(add([],(x,arr(A,B)),[(x,arr(A,B))]):-builtin),(tyc([(x,arr(A,B))],app(var(x),var(x)),B):-(tyc([(x,arr(A,B))],var(x),arr(A,B)):-(in((x,arr(A,B)),[(x,arr(A,B))]):-builtin),(unify_with_occurs_check(arr(A,B),arr(A,B)):-builtin)),(tyc([(x,arr(A,B))],var(x),arr(A,B)):-(in((x,arr(A,B)),[(x,arr(A,B))]):-builtin),(unify_with_occurs_check(arr(A,B),arr(A,B)):-builtin)),(unify_with_occurs_check(arr(A,B),A):-builtin-error),(unify_with_occurs_check(B,B):-builtin)),(unify_with_occurs_check(arr(A,B),arr(A,B)):-builtin),(unify_with_occurs_check(B,B):-builtin))
T = arr(arr(A,B),B)

yes

| ?- solve0(typ([], lam(x,app(var(x),var(x))), T), P, Ok).
solve0(typ([], lam(x,app(var(x),var(x))), T), P, Ok).

Ok = false
P = (typ([],lam(x,app(var(x),var(x))),arr(arr(A,B),B)):-(typ([(x,arr(A,B))],app(var(x),var(x)),B):-(typ([(x,arr(A,B))],var(x),arr(A,B)):-(in((x,arr(A,B)),[(x,arr(A,B))]):-builtin)),(typ([(x,arr(A,B))],var(x),arr(A,B)):-(in((x,arr(A,B)),[(x,arr(A,B))]):-builtin)),(unify_with_occurs_check(A,arr(A,B)):-builtin-error)))
T = arr(arr(A,B),B)

yes

solve0(typ([], lam(x,app(var(x),var(x))), T), P, Ok).

Ok = false
P = by(typ([],lam(x,app(var(x),var(x))),arr(arr(A,B),B)),by(typ([(x,arr(A,B))],app(var(x),var(x)),B),(by(typ([(x,arr(A,B))],var(x),arr(A,B)),by(in((x,arr(A,B)),[(x,arr(A,B))]),builtin)),by(typ([(x,arr(A,B))],var(x),arr(A,B)),by(in((x,arr(A,B)),[(x,arr(A,B))]),builtin)),error(unify_with_occurs_check(A,arr(A,B)),builtin))))
T = arr(arr(A,B),B)
