package simplifierProven.Kasim

import library._

class MySimplifier extends Simplifier{
	def simplify(x0: List[Symbol]): List[Symbol] = 
	x0 match {
  case Nil => Nil
  case Plus :: Char(x) :: t => Plus :: Char(x) :: simplify(t)
  case Plus :: Plus :: t => Qmark :: simplify(Plus :: t)
  case Plus :: Star :: t => simplify(Plus :: t)
  case Plus :: Qmark :: t => Plus :: simplify(Qmark :: t)
  case Star :: Char(x) :: t => Star :: Char(x) :: simplify(t)
  case Star :: Star :: t => simplify(Star :: t)
  case Star :: Plus :: t => simplify(Plus :: t)
  case Star :: Qmark :: t => simplify(Plus :: t)
  case Qmark :: Char(x) :: t => Qmark :: Char(x) :: simplify(t)
  case Qmark :: Plus :: t => Qmark :: simplify(Plus :: t)
  case Qmark :: Star :: t => simplify(Plus :: t)
  case Qmark :: Qmark :: t => Qmark :: simplify(Qmark :: t)
  case Char(x) :: t => Char(x) :: simplify(t)
  case List(Star) => Star :: simplify(Nil)
  case List(Qmark) => Qmark :: simplify(Nil)
  case List(Plus) => Plus :: simplify(Nil)
}

}