:- public(edge/2).
edge(a,b).
edge(b,c).
edge(c,a).

:- public(path/2).
path(X,Y) :- edge(X,Y).
path(X,Y) :- edge(X,Z), path(Z,Y).

path_clause(path(X,Y), []) :- edge(X,Y).
path_clause(path(X,Y), [path(Z,Y)]) :- edge(X,Z).

vanilla_solve([]).
vanilla_solve([G|GS]) :-
    path_clause(G,BODY),
    vanilla_solve(BODY),
    vanilla_solve(GS).

% difference list for the trace
tracer_solve([], T, T).
tracer_solve([G|GS], T_IN, T_OUT) :-
    path_clause(G,BODY),
    tracer_solve(BODY, [G|T_IN], T_OUT_BODY),
    tracer_solve(GS, T_OUT_BODY, T_OUT).

cycler_solve([], T, T).
cycler_solve([G|GS], T_IN, T_OUT) :-
    path_clause(G,BODY),
    \+ member(G, T_IN),
    cycler_solve(BODY, [G|T_IN], T_OUT_BODY),
    cycler_solve(GS, T_OUT_BODY, T_OUT).
