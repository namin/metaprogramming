% -*- Mode: Prolog -*-

% load needed files
[builtin, debug, ty].

% always print out the answers in full
set_prolog_flag(answer_write_options, [quoted(true), portray(true), spacing(next_argument)]).


% now, try each of these examples in the query REPL
/*
Note that
... ;
false.
means that we asked if we wanted more answers, said yes (;), and got none additional.
*/

ty([], lam(x, var(x)), T).
/*p
T = arr(_A, _A) ;
false.
*/

solve0(ty([], lam(x, var(x)), T), P, Ok).
/*
T = arr(_A, _A),
P = by(ty([], lam(x, var(x)), arr(_A, _A)), by(ty([(x, _A)], var(x), _A), by(in((x, _A), [(x, _A)]), builtin))),
Ok = true.
*/

ty([], lam(x,lam(y,var(x))), T).
/*
T = arr(_A, arr(_, _A)) ;
false.
*/

solve0(ty([], lam(x,lam(y,var(x))), T), P, Ok).
/*
T = arr(_A, arr(_B, _A)),
P = by(ty([], lam(x, lam(y, var(x))), arr(_A, arr(_B, _A))), by(ty([(x, _A)], lam(y, var(x)), arr(_B, _A)), by(ty([(y, _B), (x, _A)], var(x), _A), by(in((x, _A), [(y, _B), (x, _A)]), builtin)))),
Ok = true.
*/

ty([], lam(x,lam(x,var(x))), T).
/*
T = arr(_, arr(_A, _A)) ;
false.
*/

solve0(ty([], lam(x,lam(x,var(x))), T), P, Ok).
/*
T = arr(_A, arr(_B, _B)),
P = by(ty([], lam(x, lam(x, var(x))), arr(_A, arr(_B, _B))), by(ty([(x, _A)], lam(x, var(x)), arr(_B, _B)), by(ty([(x, _B), (x, _A)], var(x), _B), by(in((x, _B), [(x, _B), (x, _A)]), builtin)))),
Ok = true.
*/

ty([], lam(x,app(var(x),var(x))), T).
/*
T = arr(_S1, _A), % where
    _S1 = arr(_S1, _A) ;
false.
*/

tyc([], lam(x,app(var(x),var(x))), T).
/*
false.
*/

solve0(ty([], lam(x,app(var(x),var(x))), T), P, Ok).
/*
T = arr(_S1, _A), % where
    _S1 = arr(_S1, _A),
P = by(ty([], lam(x, app(var(x), var(x))), arr(_S1, _A)), by(ty([(x, _S1)], app(var(x), var(x)), _A), (by(ty([(x, _S1)], var(x), arr(_S1, _A)), by(in((x, arr(_S1, _A)), [(x, _S1)]), builtin)), by(ty([(x, _S1)], var(x), _S1), by(in((x, _S1), [(x, _S1)]), builtin))))),
Ok = true.
*/

solve0(tyc([], lam(x,app(var(x),var(x))), T), P, Ok).
/*
T = arr(arr(_A, _B), _B),
P = by(tyc([], lam(x, app(var(x), var(x))), arr(arr(_A, _B), _B)), (by(tyc([(x, arr(_A, _B))], app(var(x), var(x)), _B), (by(tyc([(x, arr(_A, _B))], var(x), arr(_A, _B)), (by(in((x, arr(_A, _B)), [(x, arr(_A, _B))]), builtin), by(unify_with_occurs_check(arr(_A, _B), arr(_A, _B)), builtin))), by(tyc([(x, arr(_A, _B))], var(x), arr(_A, _B)), (by(in((x, arr(_A, _B)), [(x, arr(_A, _B))]), builtin), by(unify_with_occurs_check(arr(_A, _B), arr(_A, _B)), builtin))), error(unify_with_occurs_check(arr(_A, _B), _A), builtin), by(unify_with_occurs_check(_B, _B), builtin))), by(unify_with_occurs_check(arr(_A, _B), arr(_A, _B)), builtin), by(unify_with_occurs_check(_B, _B), builtin))),
Ok = false.
*/

solve0(typ([], lam(x,app(var(x),var(x))), T), P, Ok).
/*
T = arr(arr(_A, _B), _B),
P = by(typ([], lam(x, app(var(x), var(x))), arr(arr(_A, _B), _B)), by(typ([(x, arr(_A, _B))], app(var(x), var(x)), _B), (by(typ([(x, arr(_A, _B))], var(x), arr(_A, _B)), by(in((x, arr(_A, _B)), [(x, arr(_A, _B))]), builtin)), by(typ([(x, arr(_A, _B))], var(x), arr(_A, _B)), by(in((x, arr(_A, _B)), [(x, arr(_A, _B))]), builtin)), error(unify_with_occurs_check(_A, arr(_A, _B)), builtin)))),
Ok = false.
*/

solve0(typ([], lam(x,app(var(x),var(x))), T), P, Ok).
/*
T = arr(arr(_A, _B), _B),
P = by(typ([], lam(x, app(var(x), var(x))), arr(arr(_A, _B), _B)), by(typ([(x, arr(_A, _B))], app(var(x), var(x)), _B), (by(typ([(x, arr(_A, _B))], var(x), arr(_A, _B)), by(in((x, arr(_A, _B)), [(x, arr(_A, _B))]), builtin)), by(typ([(x, arr(_A, _B))], var(x), arr(_A, _B)), by(in((x, arr(_A, _B)), [(x, arr(_A, _B))]), builtin)), error(unify_with_occurs_check(_A, arr(_A, _B)), builtin)))),
Ok = false.
*/
