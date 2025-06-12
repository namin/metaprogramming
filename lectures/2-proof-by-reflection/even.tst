comment | Proof by reflection whether a number is even |

comment | Object level |
declare indconst zro [NATNUM];
declare funconst suc (NATNUM) = NATNUM;
declare predconst Even 1;
declare indvar n [NATNUM];

axiom EVEN0: Even(zro);
axiom EVENSUC: forall n. Even(n) imp Even(suc(suc(n)));

comment | Facts we want to prove |
axiom FACT2: Even(suc(suc(zro)));
axiom FACT4: Even(suc(suc(suc(suc(zro)))));

comment | Meta level |
namecontext OBJ;
MAKECONTEXT META;
SWITCHCONTEXT META;

DECLARE PREDCONST THEOREM 1;
DECLARE SORT WFF FACT;
DECREP WFF FACT;
REPRESENT {WFF} AS WFF;
REPRESENT {FACT} AS FACT;

DECLARE FUNCONST wffof (FACT)=WFF;
ATTACH wffof TO [FACT=WFF] fact\-get\-wff;

comment | Trivial reflection - all facts become theorems |
DECLARE indvar f [FACT];
AXIOM MAKETHM: forall f. THEOREM(wffof(f));

SWITCHCONTEXT OBJ;

comment | Use reflection |
reflect MAKETHM FACT2;
theorem EVEN2 1;

reflect MAKETHM FACT4;  
theorem EVEN4 2;

show axiom;
