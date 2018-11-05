object Fold {

  // Any algebraic data type can be given a fold.

  // Here's a simple example: a type of trees with three constructors
  // for empty trees, single-element leaves, and 2-way branches:

  sealed abstract trait Tree
  case class Empty() extends Tree
  case class Leaf(x: Int) extends Tree
  case class Branch(x: Tree, y: Tree) extends Tree

  // The fold can be derived mechanically by passing a function
  // whose signature corresponds to the signature of each constructor,
  // replacing the data type Tree with the type variable A
  def fold[A] (empty : A,
               leaf : Int => A,
	       branch : A => A => A,
	       tree : Tree) : A = {
      tree match {
        case Empty() => empty
	case Leaf(x) => leaf(x)
	case Branch (x,y) => branch (fold(empty, leaf, branch, x))
				    (fold(empty, leaf, branch, y))
      }
  }
}
