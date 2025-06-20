fetch ../tst/prolegomena/appa.tst;

comment | True computational proof by reflection for even numbers - following sec91.tst pattern |
declare predconst even 1;
axiom EVEN0: even(zro);
axiom EVEN: forall n.(even(suc(suc(n))) iff even(n));

comment | Attach computational semantics |
deflam evenp(x) (= (MOD x 2) 0);
attach even to [NATNUM] evenp;

comment | Test facts |
axiom CLAIM_EVEN0: even(zro);                           comment | 0 is even - TRUE |
axiom CLAIM_EVEN2: even(suc(suc(zro)));                 comment | 2 is even - TRUE |
axiom CLAIM_EVEN4: even(suc(suc(suc(suc(zro)))));       comment | 4 is even - TRUE |
axiom CLAIM_EVEN1: even(suc(zro));                      comment | 1 is even - FALSE |

comment | Meta level setup |
NAMECONTEXT OBJ;
MAKECONTEXT META;
SWITCHCONTEXT META;

DECLARE PREDCONST THEOREM 1;
DECLARE SORT WFF FACT TERM PREDSYM FUNSYM;
DECREP WFF FACT TERM PREDSYM FUNSYM;
REPRESENT {WFF} AS WFF;
REPRESENT {FACT} AS FACT;
REPRESENT {TERM} AS TERM;
REPRESENT {PREDSYM} AS PREDSYM;
REPRESENT {FUNSYM} AS FUNSYM;

DECLARE FUNCONST wffof (FACT)=WFF;
ATTACH wffof TO [FACT=WFF] fact\-get\-wff;

comment | Following sec91 pattern exactly - declare mainpred |
DECLARE FUNCONST mainpred (WFF)=PREDSYM;
DECLARE INDCONST evenPRED [PREDSYM];
MATTACH evenPRED dar [PREDSYM] OBJ::PREDCONST:even;
DEFLAM mainpred (X) (AND (PREDAPPL X) (predappl\-get\-pred X));
ATTACH mainpred to [WFF=PREDSYM] mainpred;

comment | Following sec91 pattern - numeral checking |
DECLARE PREDCONST NUMERAL 1;
DECLARE PREDCONST numeral 3;
DECLARE INDCONST zro [TERM];
DECLARE INDCONST suc [FUNSYM];
MATTACH zro dar [TERM] OBJ::INDCONST:zro;
MATTACH suc dar [FUNSYM] OBJ::FUNCONST:suc;
DEFLAM numeral (X zro suc) (OR (EQ X zro) (AND (FUNAPPL X) (EQ (funappl\-get\-fun X) suc) (numeral (funappl1\-get\-arg X) zro suc)));
ATTACH numeral TO [TERM,TERM,FUNSYM] numeral;
DECLARE indvar x [TERM];
AXIOM AX_NUMERAL: forall x.(NUMERAL(x) iff numeral(x,zro,suc));

comment | Following sec91 pattern - mknum function |
KNOW natnums;
declare indvar n [NATNUMSORT];
DECLARE FUNCONST mknum (TERM)=NATNUMSORT;
DEFLAM mknum (X) (IF (FUNAPPL X) (ADD1 (mknum (funappl1\-get\-arg X))) 0);
ATTACH mknum TO [TERM=NATNUMREP] mknum;

comment | Define EVENCLAIM following LINEAREQ pattern |
DECLARE PREDCONST EVENCLAIM 1;
DECLARE FUNCONST arg (WFF)=TERM;
ATTACH arg TO [WFF=TERM] predappl1\-get\-arg;

DECLARE indvar w [WFF];
AXIOM AX_EVENCLAIM: forall w.(EVENCLAIM(w) iff (
  mainpred(w)=evenPRED and NUMERAL(arg(w))));

comment | The computational even checker |
DECLARE PREDCONST COMPUTEEVEN 1;
DEFLAM computeeven (t) (= (MOD (mknum t) 2) 0);
ATTACH COMPUTEEVEN TO [TERM] computeeven;

comment | Reflection principle following SOLVE pattern |
DECLARE indvar vl [FACT];
AXIOM EVENREFLECT: forall vl.(EVENCLAIM(wffof(vl)) and COMPUTEEVEN(arg(wffof(vl))) imp THEOREM(wffof(vl)));

comment | Set up simplification like sec91 |
SETBASICSIMP meta\-axioms at facts {AX_EVENCLAIM,AX_NUMERAL};
SETCOMPSIMP EVALSS AT LOGICTREE uni meta\-axioms;

SWITCHCONTEXT OBJ;

comment | Test computational reflection |
reflect EVENREFLECT CLAIM_EVEN0;
theorem THM_EVEN0 1;

reflect EVENREFLECT CLAIM_EVEN2;
theorem THM_EVEN2 2;

reflect EVENREFLECT CLAIM_EVEN4;
theorem THM_EVEN4 3;

comment | This should fail |
comment | reflect EVENREFLECT CLAIM_EVEN1; |

show axiom;