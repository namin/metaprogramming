object regexp {
  sealed abstract class Re
  sealed abstract class Num extends Re {
    def plus(that: Num): Num = this match {
      case Zero => that
      case One => One
    }
    def times(that: Num): Num = this match {
      case Zero => Zero
      case One => that
    }
  }
  case object Zero extends Num
  case object One extends Num
  case class Lit(c: Char) extends Re
  case class Times(a: Re, b: Re) extends Re
  case class Plus(a: Re, b: Re) extends Re
  case class Star(a: Re) extends Re

  def accept(r: Re, s: String): Boolean =
    acc(r, s.toList, {cs => cs match {
      case Nil => true
      case _ => false
    }})

  def acc(r: Re, cs: List[Char], k: List[Char] => Boolean): Boolean = (r,cs) match {
    case (Zero,_) => false
    case (One,_) => k(cs)
    case (Lit(d),Nil) => false
    case (Lit(d),c::cs) => if (c==d) k(cs) else false
    case (Plus(r1,r2),_) => acc(r1,cs,k) || acc(r2,cs,k)
    case (Times(r1,r2),_) => acc(r1,cs,{cp => acc(r2,cp,k)})
    case (Star(r1),_) => k(cs) || acc(r1,cs,{cp => acc(r,cp,k)})
  }

  def delta(r: Re): Num = r match {
    case Zero => Zero
    case One => One
    case Lit(_) => Zero
    case Plus(r1,r2)  => delta(r1) plus  delta(r2)
    case Times(r1,r2) => delta(r1) times delta(r2)
    case Star(_) => One
  }

  def minus(r: Re): Re = r match {
    case Zero => Zero
    case One => Zero
    case Lit(_) => r
    case Plus(r1,r2) => Plus(minus(r1),minus(r2))
    case Times(r1,r2) => Plus(Times(delta(r1),minus(r1)), Plus(Times(r1,delta(r2)), Times(minus(r1),minus(r2))))
    case Star(r) => Times(minus(r),Star(minus(r)))
  }

  def canon(r: Re): Re = Plus(delta(r), minus(r))
  def matcher(r: Re): String => Boolean = {
    val rc = canon(r)
    val m = { (s: String) => accept(rc, s) }
    m
  }
}
import regexp._

import lms.verify._
trait StagedRegexp extends Dsl with Reader with SimulatedReader {
  val table = collection.mutable.Map[Re,Rep[Input] => Rep[Boolean]]()

  def acc(r: Re, cs: Rep[Input], k: Rep[Input] => Rep[Boolean]): Rep[Boolean] = ???

  def matcher(r: Re): Rep[Input] => Rep[Boolean] = {
    val rc = canon(r)
    val m = { (s: Rep[Input]) => accept(rc, s) }
    m
  }
}

object regexp_examples {
  val ab = Times(Lit('a'), Lit('b'))
  val ac = Times(Lit('a'), Lit('c'))
  val a_or_b = Plus(Lit('a'), Lit('b'))
  val star_ab_or_ac = Star(Plus(ab, ac))
}
import regexp_examples._



class RegexpTests extends TestSuite {
  test("ab") {
    val m = matcher(ab)
    assertResult(true)(m("ab"))
    assertResult(false)(m("abc"))
    assertResult(false)(m("cab"))
    assertResult(false)(m("ac"))
  }
  test("a or b") {
    val m = matcher(a_or_b)
    assertResult(true)(m("a"))
    assertResult(true)(m("b"))
    assertResult(false)(m("c"))
    assertResult(false)(m("ab"))
    assertResult(false)(m("bc"))
  }
  test("(ab or ac)*") {
    val m = matcher(star_ab_or_ac)
    assertResult(true)(m("ab"))
    assertResult(true)(m("abac"))
    assertResult(true)(m("acab"))
    assertResult(false)(m("abca"))
    assertResult(false)(m("caba"))
    assertResult(false)(m("ad"))
  }
}

class StagedRegexpTests extends TestSuite {
  def gen(msg: String, r: Re) {
    test(msg) {
      trait RegexProg extends StagedRegexp {
        override def includes = super.includes:+"<string.h>"

        toplevel("matcher_"+msg, { s: Rep[Input] =>
          requires(valid_input(s))
          matcher(r)(s)
        }, spec=true,code=true)
      }
      check(msg, (new RegexProg with Impl).code)
    }
  }


  gen("ab", ab)
  gen("a_or_b", a_or_b)
  gen("star_ab_or_ac", star_ab_or_ac)
}
