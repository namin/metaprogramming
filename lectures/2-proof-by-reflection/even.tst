comment | Sound even reflection - only allows true facts |

comment | Object level |
declare indconst zro [NATNUM];
declare funconst suc (NATNUM) = NATNUM;
declare predconst Even 1;

comment | Mix of true and false claims |
axiom FACT_EVEN0: Even(zro);              comment | TRUE |
axiom FACT_EVEN1: Even(suc(zro));         comment | FALSE |
axiom FACT_EVEN2: Even(suc(suc(zro)));    comment | TRUE |

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

comment | Check if a fact is one we accept as true |
comment | For now, hardcode which facts are valid |
DECLARE PREDCONST ISVALID 1;
DEFLAM isvalid (f) (OR (EQUAL (fact\-get\-label f) (QUOTE FACT1)) (EQUAL (fact\-get\-label f) (QUOTE FACT3)));
ATTACH ISVALID TO [FACT] isvalid;

comment | Only valid facts become theorems |
DECLARE indvar f [FACT];
AXIOM CHECKTHM: forall f.(ISVALID(f) imp THEOREM(wffof(f)));

SWITCHCONTEXT OBJ;

comment | These should work |
reflect CHECKTHM FACT_EVEN0;
theorem EVEN0 1;

reflect CHECKTHM FACT_EVEN2;
theorem EVEN2 2;

comment | This should fail - uncomment to test |
comment | reflect CHECKTHM FACT_EVEN1; |

show axiom;
