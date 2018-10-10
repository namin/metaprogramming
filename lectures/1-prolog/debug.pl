and(false,false,false).
and(false,true,false).
and(true,false,false).
and(true,true,true).

% solve(Goals,Tree,Ok)
solve(true,true,true) :- !.
solve((A,B),(ProofA,ProofB),Ok) :- !, 
    solve(A,ProofA,OkA), solve(B,ProofB,OkB),
    and(OkA,OkB,Ok).
solve(A,by(A,builtin), true) :- builtin(A), A, !.
solve(A,error(A,builtin), false) :- builtin(A), !.
solve(A,by(A,Proof),Ok) :-
    clause(A,B), solve(B,Proof,Ok), !.
solve(A,error(A,dead),false).

solve0(A, Proof, true) :- solve(A, Proof, true), !.
solve0(A, Proof, false) :- solve(A, Proof, false).
