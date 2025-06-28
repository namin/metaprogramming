// IMP verifier, from IMP to Verification Conditions to SMT-LIB

import java.io._
import scala.sys.process._

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
}

// Z3 integration
object Z3Runner {
  def checkSat(smtScript: String): (Boolean, String) = {
    val tempFile = File.createTempFile("imp_vc_", ".smt2")
    try {
      val writer = new PrintWriter(tempFile)
      writer.write(smtScript)
      writer.close()
      
      val result = Process(scala.Seq("z3", tempFile.getAbsolutePath)).!!
      val lines = result.trim.split("\n")
      
      val isSat = lines.headOption.contains("sat")
      val isUnsat = lines.headOption.contains("unsat")
      (isSat || !isUnsat, result) // unknown are treated cautiously as sat
    } finally {
      tempFile.delete()
    }
  }
  
  def parseModel(output: String): Map[String, Int] = {
    val modelPattern = "\\(define-fun\\s+(\\w+)\\s+\\(\\)\\s+Int\\s+(\\(-\\s+\\d+\\)|\\d+)\\)".r
    val negPattern = "\\(-\\s+(\\d+)\\)".r
    modelPattern.findAllMatchIn(output).map { m =>
      val varName = m.group(1)
      val valueExpr = m.group(2)

      val value = valueExpr match {
        case negPattern(num) => -num.toInt
        case num => num.toInt
      }
      varName -> value
    }.toMap
  }
  
  def verifyVC(vc: BExpr, vars: Set[String]): (Boolean, String, String) = {
    val smtScript = checkVC(vc, vars)
    val (isSat, output) = checkSat(smtScript)
    (!isSat, output, smtScript) // VC is valid if negation is UNSAT
  }
  
  def checkVC(vc: BExpr, vars: Set[String]): String = {
    val declarations = vars.toList.sorted.map(v => s"(declare-fun $v () Int)").mkString("\n")
    
    s"""(set-logic QF_NIA)
       |$declarations
       |(assert (not ${SMTLib.toSMT(vc)}))
       |(check-sat)""".stripMargin
  }
  
  def verifyAll(vcs: List[BExpr]): List[(BExpr, String, Boolean, String, Option[Map[String, Int]])] = {
    val vars = vcs.flatMap(SMTLib.freeVars).toSet
    vcs.map { vc =>
      val (isValid, output, smtScript) = verifyVC(vc, vars)
      val model = if (!isValid && output.contains("sat")) {
        // Get model by running a separate query
        val modelScript = s"""${checkVC(vc, vars)}
                             |(get-model)""".stripMargin
        val (_, modelOutput) = checkSat(modelScript)
        Some(parseModel(modelOutput))
      } else None
      (vc, smtScript, isValid, output, model)
    }
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
    And(And(Eq(Var("i"), Num(0)), Eq(Var("s"), Num(0))), Leq(Num(0), Var("n"))),
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

  // Example 1b: Max of two numbers (bad postcondition)
  val maxProgramBogus = Program(
    True,
    If(Lt(Var("x"), Var("y")),
      Assign("m", Var("y")),
      Assign("m", Var("x"))),
    Eq(Var("m"), Var("x"))
  )
  
  def verifyProgram(name: String, prog: Program): Unit = {
    println(s"\n=== Verifying $name ===")
    println(s"\n${prettyPrint(prog)}")
    val vcs = Verifier.verify(prog)
    println(s"\nGenerated ${vcs.length} verification conditions")
    vcs.zipWithIndex.foreach { case (vc, i) =>
      println(s"\nVC ${i+1}: ${prettyPrint(vc)}")
    }
    
    try {
      // Run Z3 verification
      println(s"\nZ3 Verification:")
      println("-" * 40)

      val results = Z3Runner.verifyAll(vcs)
      var failureCount = 0
      
      results.zipWithIndex.foreach { case ((vc, smtScript, isValid, output, model), i) =>
        if (isValid) {
          println(s"✓ VC${i+1}: VALID")
        } else {
          println(s"✗ VC${i+1}: INVALID")
        }
        println("SMT Script:")
        println(smtScript)
        if (!isValid) {
          failureCount += 1
          println(s"  Failed to prove: ${prettyPrint(vc)}")
          
          model.foreach { m =>
            if (m.nonEmpty) {
              println("  Counterexample:")
              m.toList.sortBy(_._1).foreach { case (var_, value) =>
                println(s"    $var_ = $value")
              }
            }
          }
        }
      }
      
      println()
      if (failureCount == 0) {
        println(s"✓ $name: VERIFICATION SUCCESSFUL")
      } else {
        println(s"✗ $name: VERIFICATION FAILED ($failureCount invalid VC(s))")
      }
      
    } catch {
      case e: Exception =>
        println(s"❌ Error running Z3: ${e.getMessage}")
        println("Make sure Z3 is installed and in your PATH")
    }
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
  verifyProgram("MaxBogus", maxProgramBogus)
}
