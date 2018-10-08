package intro_done

object tests extends App {
  import implicits._

  import pimp._
  def st = new java.util.StringTokenizer("this is a test");
  assert(st.all==List("this", "is", "a", "test"))
  assert(st.all(_.length)==List(4, 2, 1, 4))

  assert(intOrdering.compare(3,7) < 0)

  val xs1 = quicksort(List(2,9,3,8,1))
  assert(xs1 == List(1,2,3,8,9))
  val xs2 = quicksort(List(2,9,3,8,1))(reverse(intOrdering))
  assert(xs2 == List(9,8,3,2,1))
  val xs3 = List(2,9,3,8,1).quicksort
  assert(xs3 == List(1,2,3,8,9))
  val xs4 = List(2,9,3,8,1).quicksort(intOrdering.reverse)
  assert(xs4 == List(9,8,3,2,1))

  import lambda_calc._
  assert(ev(App(Lam(Var("x"), Var("x")), Const(1)), Map()) == Const(1))

  import sugar._
  assert(AboutHalf(3)==1)
  assert((3 match { case AboutHalf(x) => x }) == 1)

  assert((2 match { case Half(x) => x  case _ => -1 }) ==  1)
  assert((3 match { case Half(x) => x  case _ => -1 }) == -1)

  assert(6 == (720 match { case Factorial(x) => x }))

  import trait_delegation._
  assert((new A with B with C {}).hello == "yay! my dear friend, hello, world! yay!")
  assert((new B with C with A {}).hello == "my dear friend, yay! hello, world! yay!")
  assert((new C with B with A {}).hello == "my dear friend, yay! hello yay!, world!")
}

object implicits {
  // implicit conversions
  // ex: complex numbers, promoting int

  case class Complex(r: Int, i: Int) {
    val a = this
    def +(b: Complex) =
      Complex(a.r+b.r, a.i+b.i)
    def -(b: Complex) = ???
    def *(b: Complex) = ???
    override def toString = s"($r + ${i}i)"
  }

  object Complex {
    implicit def fromInt(r: Int) = Complex(r, 0)
  }

  // ex: pimp library, infix methods
  object pimp {
    def all2list(it: java.util.StringTokenizer) = {
      val buf = new scala.collection.mutable.ListBuffer[String]()
      while (it.hasMoreTokens) {
        buf += it.nextToken
      }
      buf.toList
    }
    implicit class PimpedOps[A](it: java.util.StringTokenizer) {
      def all: List[String] = all2list(it)
      def all[B](f: String => B): List[B] = all.map(f)
    }
  }

  // implicit parameters
  // ex: type classes

  // type classes, e.g. Numeric[T], Ordering[T]
  def foo[T:Numeric](x: T) = {
    val num = implicitly[Numeric[T]]
    num.plus(x, x)
  }
  // equivalently:
  def foo2[T](x: T)(implicit num: Numeric[T]) {
    num.plus(x,x)
  }
  // for example, we could define Numeric[Complex]
  implicit def numComplex: Numeric[Complex] = ???

  // here is another example
  // taken from
  // https://github.com/namin/implicits-demo/blob/master/src/test/scala/test.scala

  abstract class Ordering[A] {
    def compare(x:A,y:A): Int
  }

  implicit object intOrdering extends Ordering[Int] {
    def compare(x:Int,y:Int) = x-y
  }

  implicit object stringOrdering extends Ordering[String] {
    def compare(x:String,y:String) = x.compareTo(y)
  }

  def implicitly[T](implicit e: T) = e

  def ordering[T](implicit e: Ordering[T]) = e

  // the `T:Ordering` is typeclass-inspired syntactic sugar
  // for an additional implicit requirement:
  // def quicksort[T](xs: List[T])(implicit e: Ordering[T])
  def quicksort[T:Ordering](xs: List[T]): List[T] = xs match {
    case Nil => Nil
    case p::xs =>
      val (as,bs) = xs.partition(x => ordering[T].compare(x,p) < 0)
      quicksort(as) ++ (p::quicksort(bs))
  }

  def reverse[A](o: Ordering[A]) = new Ordering[A] {
    def compare(x:A,y:A) = - o.compare(x,y)
  }

  // instead of the function syntax quicksort() we may want to use
  // xs.quicksort: let's use pimp my library again

  implicit class RichList[T](xs:List[T]) {
    def quicksort(implicit ev: Ordering[T]): List[T] = xs match {
      case Nil => Nil
      case p::xs =>
        val (as,bs) = xs.partition(x => ev.compare(x,p) < 0)
        as.quicksort ++ (p::bs.quicksort)
    }
  }

  implicit class RichOrdering[A](o: Ordering[A]) {
    def reverse = new Ordering[A] {
      def compare(x:A,y:A) = - o.compare(x,y)
    }
  }

  // ex: source context, manifests, type tags...
}

object lambda_calc {
  // sealed case classes
  // ex: mini lambda-calculus interpreter

  sealed abstract trait Term
  sealed abstract trait Val
  case class Var(x: String) extends Term
  case class Lam(p: Var, b: Term) extends Term
  case class App(a: Term, b: Term) extends Term

  type Env = Map[Var,Val]
  case class Clo(l: Lam, m: Env) extends Val
  case class Const(n: Int) extends Term with Val

  def ev(e: Term, m: Env): Val = e match {
    case v@Var(x) => m(v)
    case c@Const(n) => c
    case l@Lam(p, b) => Clo(l, m)
    case App(a, b) => ev(a, m) match {
      case Clo(Lam(param, body), clo_env) =>
        val arg = ev(b, m)
        ev(body, clo_env + (param -> arg))
    }
  }
}

object sugar {
  // apply/unapply
  // ex: custom pattern matching

  object AboutHalf {
    def apply(r: Int) = r/2
    def unapply(r: Int): Some[Int] = Some(r/2)
  }

  object Half {
    def unapply(r: Int): Option[Int] =
      if (r % 2 == 0) Some(r/2) else None
  }

  object Factorial {
    def apply(n: Int): Int = if (n == 0) 1 else n*Factorial(n-1)
    def unapply(r: Int): Option[Int] =
      if (r < 0) None
      else {
        val xs = (0 to r).collect{case x if Factorial(x) == r => x}
        if (xs.isEmpty) None else Some(xs(0))
      }
  }

  // case class to companion object
  case class Foo(a: Int)
  // produces companion object
  object Foo {
    def apply(a: Int): Foo = Foo(a)
    def unapply(x: Foo): Some[Int] = Some(x.a)
  }
}

object trait_delegation {
  // trait
  // ex: delegation
  trait O {
    def hello: String = "hello"
  }
  trait A extends O {
    override def hello: String = "my dear friend, " + super.hello
  }
  trait B extends O {
    override def hello: String = super.hello + ", world!"
  }
  trait C extends O {
    override def hello: String = "yay! " + super.hello + " yay!"
  }
}
