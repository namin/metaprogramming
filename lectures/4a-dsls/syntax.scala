// Tagless-final definition of a little language, lambda calculus with
// addition and booleans

object Syntax {

  // We'll define the syntax for a little language in a modular
  // fashion.  Each part of the language is defined separately,
  // and the parts are combined later

  // Integers with addition.  The definition is abstracted over the
  // 'interpretation' T.  Later we'll instantiate T with various
  // different types to give a variety of interpretations to Add.
  trait Add[T[_]] {
    def int : Int => T[Int]
    // 'int' represents integer constants.  It constructs a term of
    // type Int from an integer value

    def add : T[Int] => T[Int] => T[Int]
    // 'add' represents addition expressions.  It constructs a term of
    // type Int (the sum) from two terms of type Int (the summands)
  }

  // Booleans with branching.  As with Add, we abstract over the
  // interpretation T
  trait Bools[T[_]] {
    def bool : Boolean => T[Boolean]
    // 'bool' represents boolean constants.  It constructs a term of
    // type Bool from a boolean value

    def if_[A] : T[Boolean] => (() => T[A]) => (() => T[A]) => T[A]
    // 'if_' represents if expressions.  It constructs a term of
    // type T[A] (for some A) from a boolean term and two delayed
    // terms of type A (the 'then' and 'else' branches)
  }

  // Lambda expressions, using Higher Order Abstract Syntax
  trait Lambda[T[_]] {
    def lam[A,B] : (T[A] => T[B]) => T[A => B]
    // 'lam' represents lambda terms λx.e
    // The body 'e' is represented as a function that
    // accepts the argument term as its argument.
    // Looked at another way, 'lam' turns a host-language function
    // into an object-language function.

    def app[A, B] : T[A => B] => (T[A] => T[B])
    // 'app' represents application terms f p
    // There are two arguments: a term of type A => B
    //                      and a term of type A.
    // The constructed term has type B.
    // Looked at another way, 'app' turns an object language function
    // into a host language function
  }

  // Scala's mixin composition allows us to seamlessly combine the 
  // little languages into a larger language.
  //
  // Other languages have similar facilities (e.g. type classes in
  // Haskell, modules in ML/OCaml)
  trait Exp[T[_]] extends Bools[T] with Add[T] with Lambda[T];

  // An example term, abstracted over the interpretation 's' and its type 'T'.
  def example1[T[_]](s:Exp[T]) : T[Int] = {
    import s._
    // the term is
    //    if true then 3 + 4
    //    else 5
    (if_(bool(true))
      (() => (add(int(3)) (int(4))))
      (() => int(5)))
  }
  // Later we can apply 'example1' to an instance of 'Exp' to interpret the term.

  // An evaluator interpretation.  The type T is instantiated with the identity
  // so that T[Int] becomes Int, T[A=>B] becomes A=>B, and so on.
  type Id[A] = A
  implicit object Eval extends Exp[Id] {
    // The implementation of the various functions is trivial:
    //   addition is just host language addition, and so on.
    def add: Int => Int => Int =
            x => y => x + y
    def int:  Int => Int =
            x => x
    def bool : Boolean => Boolean =
            b => b
    def if_[A] : Boolean => (() => A) => (() => A) => A =
            b => t => e => if (b) { t () } else { e () }
    def lam[A, B] = (f : A => B) => f
    def app[A, B] = (f : A => B) => (p : A) => f(p)
  }

  // A pretty-printer interpretation.  The type T is instantiated with
  // the constant function that returns String, so that T[Int] becomes String,
  // T[A=>B] becomes String, and so on.
  type CString[A] = String
  implicit object Show extends Exp[CString] {
    // Each function constructs a string representation of the
    // corresponding term from the argument strings
    // For example, 'add' takes two strings representing the summands
    // and builds a string representing the sum.
    def add: String => String => String =
            x => y => "("+ x + " + " + y + ")"
    def int:  Int => String =
            x => x.toString
    def bool : Boolean => String =
            b => b.toString
    def if_[A] : String => (() => String) => (() => String) => String =
            b => t => e =>
            "(if "+ b +" then "+ t() +" else "+ e() +")"
    var counter = 1
    def lam[A, B] = (f : String => String) => {
      val x = s"x$counter"
      counter += 1
      val body = f(x)
      s"\\$x.$body"
    }
    def app[A,B] = (f : String) => (p : String) => s"($f $p)"
  }

  // A second example, again abstracted over the interpretation 's'
  // and its type.
  def example2[T[_]](s:Exp[T]) : T[(Int => Int) => (Int => Int)] = {
    import s._
    // The example term is λf.λx.f (f x)
    lam[Int => Int,Int => Int] (f =>
      lam[Int,Int] (x => 
        app (f) (app(f)(x))))
  }
}

