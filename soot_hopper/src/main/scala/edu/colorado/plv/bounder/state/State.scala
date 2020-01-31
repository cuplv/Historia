package edu.colorado.plv.bounder.state

import edu.colorado.plv.bounder.solver.Z3Solver

object State {
  private var id:Int = -1
  def getId():Int = {
    id = id + 1
    id
  }
  val solver = new Z3Solver()
}

// pureFormula is a conjunction of constraints
// callStack is the call string from thresher paper
case class State(callStack: List[CallStackFrame],pureFormula: Set[PureConstraint]) {
  val solver = new Z3Solver()
  def isFeasible:Boolean = solver.isFeasible(this)
  override def toString:String = {
    val stackString = callStack.headOption match{
      case Some(sf) => {

        val locals: Map[StackVar, Val] = sf.locals
        sf.toString() + " locals: " + locals.map(k => k._1.toString + " -> " + k._2.toString).mkString(",")
      }
      case None => "[nc]"
    }
    val pureFormulaString = "   pure: " + pureFormula.map(a => a.toString).mkString(" && ")
    s"($stackString   $pureFormulaString)"
  }
}

sealed trait Val
//case object TopVal extends Val
//case object NullVal extends Val
//
///**
// * Val that is instantiated from a subtype of className
// */
//case class ObjSubtypeVal(className:String) extends Val{
//  val id = State.getId()
//}

sealed trait Var // Var in the program
case class StackVar(name : String) extends Var{
  override def toString:String = name
}

sealed trait CmpOp
case object Equals extends CmpOp{
  override def toString:String = " == "
}
case object NotEquals extends CmpOp{
  override def toString:String = " != "
}

sealed trait PureConstraint
case class PureAtomicConstraint(lhs:PureExpr, op: CmpOp, rhs:PureExpr) extends PureConstraint {
  override def toString:String = s"$lhs $op $rhs"
}

sealed abstract class PureExpr {
  def substitute(toSub : PureExpr, subFor : PureVar) : PureExpr
  def isStringExpr : Boolean = false
  def isBitwiseExpr : Boolean = false
  def isFloatExpr : Boolean = false
  def isLongExpr : Boolean = false
  def isDoubleExpr : Boolean = false
  def getVars(s : Set[PureVar] = Set.empty) : Set[PureVar]
}




// constant values
sealed abstract class PureVal(val v : Any) extends PureExpr {
  override def substitute(toSub : PureExpr, subFor : PureVar) : PureVal = this

  def >(p : PureVal) : Boolean = sys.error("GT for arbitrary PureVal")
  def <(p : PureVal) : Boolean = sys.error("LT for arbitrary PureVal")
  def >=(p : PureVal) : Boolean = sys.error("GE for arbitrary PureVal")
  def <=(p : PureVal) : Boolean = sys.error("LE for arbitrary PureVal")
  override def isStringExpr : Boolean = ??? //this.isInstanceOf[StringVal]
  override def getVars(s : Set[PureVar] = Set.empty) : Set[PureVar] = s

  override def hashCode : Int = ???
  override def equals(other : Any) : Boolean = other match {
    case p : PureVal => this.v == p.v
    case _ => false
  }
  override def toString : String = v.toString
}
case object NullVal extends PureVal{
  override def toString:String = "NULL"
}
//TODO: do we need type constraints here?
case class ClassVal() extends PureVal

// pure var is a symbolic var (e.g. this^ from the paper)
sealed case class PureVar(typ : String) extends PureExpr with Val {
  val id : Int = State.getId()

//  override def isArrayType : Boolean = false
  override def isStringExpr : Boolean = typ == "java.lang.String"
  override def isFloatExpr : Boolean = typ == ???
  override def isLongExpr : Boolean = typ == ???
  def isReferenceType : Boolean = ???

  // TODO: should we ask Z3 here? may be sound to do something coarser if we are careful about our usage of this
  def |=(other : Val) : Boolean = other match {
    case PureVar(oType) => typ == oType // this == other
    case _ => false
  }
  override def getVars(s : Set[PureVar]) : Set[PureVar] = s + this

  override def substitute(toSub : PureExpr, subFor : PureVar) : PureExpr = if (subFor == this) toSub else this

  override def hashCode : Int = id*100271
  override def equals(other : Any) : Boolean = other match {
    case p : PureVar => this.id == p.id
    case _ => false
  }
  override def toString : String = "p-" + id
}