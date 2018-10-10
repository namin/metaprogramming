%% Environment, with shadowing

in((X,A),G) :- member((X,A),G), !.

%% Typing rules in lambda-calculus

%%  x:A in G
%% ---------- tvar
%% G |- x : A

%%  G,x:A |- M : B
%% ----------------- ->-intro
%% G |- lambdax.M : A->B

%% G |- M : A->B
%% G |- N : A
%% ------------- ->-elim
%% G |- M N : B

:- public(ty/3).
ty(G, var(X), A) :- in((X,A), G).
ty(G, lam(X,M), arr(A,B)) :- ty([(X,A)|G],M,B).
ty(G, app(M,N), B) :- ty(G, M, arr(A,B)), ty(G, N, A).

:- public(tyc/3).
tyc(G, var(X), A1) :- in((X,A2), G),
  unify_with_occurs_check(A1,A2).
tyc(G, lam(X,M), arr(A1,B1)) :- tyc([(X,A2)|G],M,B2),
  unify_with_occurs_check(A1,A2), unify_with_occurs_check(B1,B2).
tyc(G, app(M,N), B1) :- tyc(G, M, arr(A2,B2)), tyc(G, N, A1),
  unify_with_occurs_check(A1,A2), unify_with_occurs_check(B1,B2).

:- public(typ/3).
typ(G, var(X), A) :- in((X,A), G).
typ(G, lam(X,M), arr(A,B)) :- typ([(X,A)|G],M,B).
typ(G, app(M,N), B) :- typ(G, M, arr(A1,B)), typ(G, N, A2),
  unify_with_occurs_check(A1,A2).
