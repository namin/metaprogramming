object Tagged {

  // A 'tagged' implementation of the language of integers with addition
  sealed abstract trait Exp;
  case class Lit(x:Int) extends Exp;
  case class Add(x:Exp, y:Exp) extends Exp;

  // Evaluation is implemented via recursion and case analysis
  def eval(e : Exp) : Int = {
    e match {
       case Lit(x) => x
       case Add(x,y) => eval(x) + eval(y)
    }
  }

  // We can also implement evaluation (and other functions, such as
  // pretty-printing) using folds over the syntax.
  def fold[A] (lit : Int => A, add : A => A => A, exp : Exp) : A = {
    exp match {
      case Lit(x) => lit(x) 
      case Add(x,y) => add(fold(lit, add, x))
                          (fold(lit, add, y))
    }
  }

  def eval2(e: Exp) = fold(x => x,
                           x => y => x + y,
                           e)
}
