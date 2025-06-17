// IMP verifier, from IMP to Verification Conditions to SMT-LIB

// AST definitions
sealed trait AExpr
case class Num(n: Int) extends AExpr
case class Var(x: String) extends AExpr
case class Plus(a1: AExpr, a2: AExpr) extends AExpr
case class Minus(a1: AExpr, a2: AExpr) extends AExpr
case class Times(a1: AExpr, a2: AExpr) extends AExpr

sealed trait BExpr
case object True extends BExpr
case object False extends BExpr
case class Eq(a1: AExpr, a2: AExpr) extends BExpr
case class Lt(a1: AExpr, a2: AExpr) extends BExpr
case class Leq(a1: AExpr, a2: AExpr) extends BExpr
case class Not(b: BExpr) extends BExpr
case class And(b1: BExpr, b2: BExpr) extends BExpr
case class Or(b1: BExpr, b2: BExpr) extends BExpr
case class Implies(b1: BExpr, b2: BExpr) extends BExpr

sealed trait Stmt
case object Skip extends Stmt
case class Assign(x: String, a: AExpr) extends Stmt
case class Seq(s1: Stmt, s2: Stmt) extends Stmt
case class If(b: BExpr, s1: Stmt, s2: Stmt) extends Stmt
case class While(b: BExpr, inv: BExpr, s: Stmt) extends Stmt

case class Program(pre: BExpr, stmt: Stmt, post: BExpr)

// Verification condition generation with integrated weakest precondition
object Verifier {
  
  def substitute(e: AExpr, x: String, a: AExpr): AExpr = e match {
    case Num(n) => Num(n)
    case Var(y) => if (x == y) a else Var(y)
    case Plus(a1, a2) => Plus(substitute(a1, x, a), substitute(a2, x, a))
    case Minus(a1, a2) => Minus(substitute(a1, x, a), substitute(a2, x, a))
    case Times(a1, a2) => Times(substitute(a1, x, a), substitute(a2, x, a))
  }
  
  def substitute(b: BExpr, x: String, a: AExpr): BExpr = b match {
    case True => True
    case False => False
    case Eq(a1, a2) => Eq(substitute(a1, x, a), substitute(a2, x, a))
    case Lt(a1, a2) => Lt(substitute(a1, x, a), substitute(a2, x, a))
    case Leq(a1, a2) => Leq(substitute(a1, x, a), substitute(a2, x, a))
    case Not(b1) => Not(substitute(b1, x, a))
    case And(b1, b2) => And(substitute(b1, x, a), substitute(b2, x, a))
    case Or(b1, b2) => Or(substitute(b1, x, a), substitute(b2, x, a))
    case Implies(b1, b2) => Implies(substitute(b1, x, a), substitute(b2, x, a))
  }
  
  // Combined wp and vcgen -- returns (weakest precondition, verification conditions)
  def wpVc(s: Stmt, q: BExpr): (BExpr, List[BExpr]) = s match {
    case Skip => 
      (q, Nil)
    
    case Assign(x, a) => 
      (substitute(q, x, a), Nil)
    
    case Seq(s1, s2) =>
      val (wp2, vcs2) = wpVc(s2, q)
      val (wp1, vcs1) = wpVc(s1, wp2)
      (wp1, vcs1 ++ vcs2)
    
    case If(b, s1, s2) =>
      val (wp1, vcs1) = wpVc(s1, q)
      val (wp2, vcs2) = wpVc(s2, q)
      (And(Implies(b, wp1), Implies(Not(b), wp2)), vcs1 ++ vcs2)
    
    case While(b, inv, s) =>
      val (wpBody, vcsBody) = wpVc(s, inv)
      val vcInv = Implies(And(inv, b), wpBody)  // invariant preserved
      val vcExit = Implies(And(inv, Not(b)), q) // exit condition
      (inv, vcInv :: vcExit :: vcsBody)
  }
  
  def verify(prog: Program): List[BExpr] = {
    val (wp, vcs) = wpVc(prog.stmt, prog.post)
    Implies(prog.pre, wp) :: vcs
  }
}

// SMT-LIB generation
object SMTLib {
  
  def toSMT(e: AExpr): String = e match {
    case Num(n) => n.toString
    case Var(x) => x
    case Plus(a1, a2) => s"(+ ${toSMT(a1)} ${toSMT(a2)})"
    case Minus(a1, a2) => s"(- ${toSMT(a1)} ${toSMT(a2)})"
    case Times(a1, a2) => s"(* ${toSMT(a1)} ${toSMT(a2)})"
  }
  
  def toSMT(b: BExpr): String = b match {
    case True => "true"
    case False => "false"
    case Eq(a1, a2) => s"(= ${toSMT(a1)} ${toSMT(a2)})"
    case Lt(a1, a2) => s"(< ${toSMT(a1)} ${toSMT(a2)})"
    case Leq(a1, a2) => s"(<= ${toSMT(a1)} ${toSMT(a2)})"
    case Not(b1) => s"(not ${toSMT(b1)})"
    case And(b1, b2) => s"(and ${toSMT(b1)} ${toSMT(b2)})"
    case Or(b1, b2) => s"(or ${toSMT(b1)} ${toSMT(b2)})"
    case Implies(b1, b2) => s"(=> ${toSMT(b1)} ${toSMT(b2)})"
  }
  
  def freeVars(e: AExpr): Set[String] = e match {
    case Num(_) => Set.empty
    case Var(x) => Set(x)
    case Plus(a1, a2) => freeVars(a1) ++ freeVars(a2)
    case Minus(a1, a2) => freeVars(a1) ++ freeVars(a2)
    case Times(a1, a2) => freeVars(a1) ++ freeVars(a2)
  }
  
  def freeVars(b: BExpr): Set[String] = b match {
    case True | False => Set.empty
    case Eq(a1, a2) => freeVars(a1) ++ freeVars(a2)
    case Lt(a1, a2) => freeVars(a1) ++ freeVars(a2)
    case Leq(a1, a2) => freeVars(a1) ++ freeVars(a2)
    case Not(b1) => freeVars(b1)
    case And(b1, b2) => freeVars(b1) ++ freeVars(b2)
    case Or(b1, b2) => freeVars(b1) ++ freeVars(b2)
    case Implies(b1, b2) => freeVars(b1) ++ freeVars(b2)
  }
  
  def generateScript(vcs: List[BExpr]): String = {
    val vars = vcs.flatMap(freeVars).toSet
    val declarations = vars.toList.sorted.map(v => s"(declare-fun $v () Int)").mkString("\n")
    
    val assertions = vcs.zipWithIndex.map { case (vc, i) =>
      s"; VC ${i + 1}\n(assert (not ${toSMT(vc)}))"
    }.mkString("\n")
    
    s"""(set-logic QF_NIA)
       |$declarations
       |$assertions
       |(check-sat)""".stripMargin
  }
}

// Example programs and main
object Main extends App {
  
  // Example 1: Max of two numbers
  val maxProgram = Program(
    True,
    If(Lt(Var("x"), Var("y")),
       Assign("m", Var("y")),
       Assign("m", Var("x"))),
    And(Or(Eq(Var("m"), Var("x")), Eq(Var("m"), Var("y"))),
        And(Leq(Var("x"), Var("m")), Leq(Var("y"), Var("m"))))
  )
  
  // Example 2: Simple counter
  val counterProgram = Program(
    Eq(Var("x"), Num(0)),
    Seq(
      Assign("x", Plus(Var("x"), Num(1))),
      Assign("x", Plus(Var("x"), Num(1)))
    ),
    Eq(Var("x"), Num(2))
  )
  
  // Example 3: Loop with invariant
  val loopProgram = Program(
    And(Eq(Var("i"), Num(0)), Eq(Var("s"), Num(0))),
    While(
      Lt(Var("i"), Var("n")),
      And(Leq(Num(0), Var("i")), Leq(Var("i"), Var("n"))), // invariant
      Seq(
        Assign("s", Plus(Var("s"), Var("i"))),
        Assign("i", Plus(Var("i"), Num(1)))
      )
    ),
    Eq(Var("i"), Var("n"))
  )
  
  def verifyProgram(name: String, prog: Program): Unit = {
    println(s"\n=== Verifying $name ===")
    println(s"\n${prettyPrint(prog)}")
    val vcs = Verifier.verify(prog)
    println(s"\nGenerated ${vcs.length} verification conditions")
    vcs.zipWithIndex.foreach { case (vc, i) =>
      println(s"\nVC ${i+1}: ${prettyPrint(vc)}")
    }
    println(s"\nSMT-LIB script:\n${SMTLib.generateScript(vcs)}")
  }
  
  def prettyPrint(b: BExpr): String = b match {
    case True => "true"
    case False => "false"
    case Eq(a1, a2) => s"${prettyPrint(a1)} = ${prettyPrint(a2)}"
    case Lt(a1, a2) => s"${prettyPrint(a1)} < ${prettyPrint(a2)}"
    case Leq(a1, a2) => s"${prettyPrint(a1)} <= ${prettyPrint(a2)}"
    case Not(b1) => s"!${prettyPrint(b1)}"
    case And(b1, b2) => s"(${prettyPrint(b1)} && ${prettyPrint(b2)})"
    case Or(b1, b2) => s"(${prettyPrint(b1)} || ${prettyPrint(b2)})"
    case Implies(b1, b2) => s"(${prettyPrint(b1)} => ${prettyPrint(b2)})"
  }
  
  def prettyPrint(a: AExpr): String = a match {
    case Num(n) => n.toString
    case Var(x) => x
    case Plus(a1, a2) => s"${prettyPrint(a1)} + ${prettyPrint(a2)}"
    case Minus(a1, a2) => s"${prettyPrint(a1)} - ${prettyPrint(a2)}"
    case Times(a1, a2) => s"${prettyPrint(a1)} * ${prettyPrint(a2)}"
  }
  
  def prettyPrint(s: Stmt, indent: Int = 0): String = {
    val spaces = "  " * indent
    s match {
      case Skip => s"${spaces}skip"
      case Assign(x, a) => s"${spaces}$x := ${prettyPrint(a)}"
      case Seq(s1, s2) => s"${prettyPrint(s1, indent)};\n${prettyPrint(s2, indent)}"
      case If(b, s1, s2) => 
        s"${spaces}if (${prettyPrint(b)}) then\n${prettyPrint(s1, indent + 1)}\n${spaces}else\n${prettyPrint(s2, indent + 1)}"
      case While(b, inv, s) =>
        s"${spaces}while (${prettyPrint(b)})\n${spaces}  inv: ${prettyPrint(inv)}\n${spaces}do\n${prettyPrint(s, indent + 1)}"
    }
  }
  
  def prettyPrint(prog: Program): String = {
    s"Precondition:  ${prettyPrint(prog.pre)}\n" +
    s"Program:\n${prettyPrint(prog.stmt)}\n" +
    s"Postcondition: ${prettyPrint(prog.post)}"
  }
  
  // Run examples
  verifyProgram("Max", maxProgram)
  verifyProgram("Counter", counterProgram)
  verifyProgram("Loop", loopProgram)
}
