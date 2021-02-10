package edu.colorado.plv.bounder.lifestate

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.MessageType
import edu.colorado.plv.bounder.lifestate.LifeState.{And, I, LSFalse, LSPred, LSSpec, LSTrue, NI, Not, Or}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BoolVal, CmpOp, Equals, NullVal, PureExpr, PureVal}

import scala.util.parsing.combinator._
import upickle.default.{macroRW, ReadWriter => RW}

object LifeState extends RegexParsers {
  var id = 0
  def nextLsVar():String = {
    val lsVar = "v" + id
    id = id+1
    lsVar
  }

  // Const value matchers
  val LSBoolConst = "@(false|true|False|True)".r
  val LSNullConst = "@(?:null|Null|NULL)".r
  object LSConst{
    def unapply(arg: String): Option[PureVal] = arg match{
      case LSBoolConst(sv) => Some(BoolVal(sv.toBoolean))
      case LSNullConst() => Some(NullVal)
      case _ => None
    }
  }
  val LSVar = "((?:[a-zA-Z])(?:[a-zA-Z0-9]|_)*)".r


  val LSAnyVal = "_".r

  case class LSConstraint(v1:String,op:CmpOp,v2:String )

  sealed trait LSPred {
    def contains(mt:MessageType,sig: (String, String)):Boolean

    def lsVar: Set[String]
  }
  object LSPred{
    implicit var rw:RW[LSPred] = RW.merge(LSAtom.rw, macroRW[Not], macroRW[And],
      macroRW[Or], macroRW[LSTrue.type], macroRW[LSFalse.type])
  }

  val LSGenerated = "LS_GENERATED_.*".r

  case class And(l1 : LSPred, l2 : LSPred) extends LSPred {
    override def lsVar: Set[String] = l1.lsVar.union(l2.lsVar)
    override def toString:String = s"(${l1.toString} AND ${l2.toString})"

    override def contains(mt:MessageType, sig: (String, String)): Boolean = l1.contains(mt,sig) || l2.contains(mt,sig)
  }
  case class Not(l: LSPred) extends LSPred {
    override def lsVar: Set[String] = l.lsVar
    override def toString:String = s"(NOT ${l.toString})"

    override def contains(mt:MessageType,sig: (String, String)): Boolean = l.contains(mt,sig)
  }
  case class Or(l1:LSPred, l2:LSPred) extends LSPred {
    override def lsVar: Set[String] = l1.lsVar.union(l2.lsVar)
    override def toString:String = s"(${l1.toString} OR ${l2.toString})"
    override def contains(mt:MessageType,sig: (String, String)): Boolean = l1.contains(mt, sig) || l2.contains(mt,sig)
  }
  case object LSTrue extends LSPred {
    override def lsVar: Set[String] = Set.empty
    override def contains(mt:MessageType,sig: (String, String)): Boolean = false
  }
  case object LSFalse extends LSPred {
    override def lsVar: Set[String] = Set.empty
    override def contains(mt:MessageType,sig: (String, String)): Boolean = false
  }

  sealed trait LSAtom extends LSPred {
    def getAtomSig:String
    def identitySignature:String
  }
  object LSAtom{
    implicit val rw:RW[LSAtom] = RW.merge(I.rw, NI.rw)
  }

  // A method with a signature in "signatures" has been invoed
  // lsVars: element 0 is return value, element 1 is reciever, rest of the elements are arguemnts
  // A string of "_" means "don't care"
  // primitives are parsed as in java "null", "true", "false", numbers etc.
  case class I(mt: MessageType, signatures: Set[(String, String)], lsVars : List[String]) extends LSAtom {
    def constVals(constraints: Set[LSConstraint]):List[Option[(CmpOp, PureExpr)]] = lsVars.map{
      case LifeState.LSConst(v) => Some((Equals, v))
      case LifeState.LSVar(v) =>
        constraints.find(c => c.v1 == v || c.v2 == v) match {
          case Some(LSConstraint(_, op, LifeState.LSConst(v2))) => Some(op,v2)
          case Some(LSConstraint(LifeState.LSConst(v1), op, _)) => Some(op,v1)
          case None => None
          case c => throw new IllegalStateException(s"Malformed constraint: $c")
        }
      case _ => None
    }
    private val sortedSig = signatures.toList.sorted
    override def lsVar: Set[String] = lsVars.filter(vname => LifeState.LSVar.matches(vname)).toSet

    def getVar(i: Int): String = lsVars(i)


    override def getAtomSig: String = {
      s"I(${sortedSig.mkString(":")})"
    }

    // Uesed for naming uninterpreted functions in z3 solver
    override def identitySignature: String = {
      // Note: this does not include varnames or
      // any other info that would distinguish this I from another with the same metods
      s"I_${mt.toString}_${sortedSig.head._1}_${sortedSig.head._2}"
    }
    override def toString:String = s"I($mt $identitySignature ( ${lsVars.mkString(",")} )"

    override def contains(omt:MessageType,sig: (String, String)): Boolean = signatures.contains(sig) && omt == mt
  }
  object I{
    implicit val rw:RW[I] = macroRW
  }
  // Since i1 has been invoked, i2 has not been invoked.
  case class NI(i1:I, i2:I) extends LSAtom{
    def lsVar: Set[String] = i1.lsVar.union(i2.lsVar)

    override def getAtomSig: String = s"NI(${i1.getAtomSig}, ${i2.getAtomSig})"

    override def identitySignature: String = s"${i1.identitySignature}_${i2.identitySignature}"
    override def toString:String = s"NI( ${i1.toString} , ${i2.toString} )"

    override def contains(mt:MessageType,sig: (String, String)): Boolean = i1.contains(mt, sig) || i2.contains(mt, sig)
  }
  object NI{
    implicit val rw:RW[NI] = macroRW
  }
  case class LSSpec(pred:LSPred, target: I, rhsConstraints: Set[LSConstraint] = Set())

  // Class that holds a graph of possible predicates and alias relations between the predicates.
  // Generated from a fast pre analysis of the applications.
  // Set of vars that can alias are represented by having the same name.
  class PredicateSpace(predicates: Set[LSAtom]){
    /** mapping from variable names to predicates containing variable */
    val findVars: Map[String, Set[LSAtom]] = predicates.foldLeft(Map[String, Set[LSAtom]]()) { (acc, v) =>
      v.lsVar.foldLeft(acc){ (iacc, varname) => iacc + (varname -> (iacc.getOrElse(varname, Set()) + v) )}
    }

    /**
     *
     * @param src source of alias edge (index, atom sig)
     * @param tgt target of alias edge (index, atom sig)
     */
    case class Edge(src: (Int, String), tgt: (Int, String))

    def getEdgeSet: Set[Edge] = {
      val varmap: Map[String, Set[(Int, String)]] =
        predicates.foldLeft(Map[String, Set[(Int,String)]]()) { (acc, predicate) => {
          predicate.lsVar.zipWithIndex.foldLeft(acc){(iacc, v) => {
            val oldSet: Set[(Int, String)] = iacc.getOrElse(v._1, Set())
            val newPar: (Int, String) = (v._2, predicate.getAtomSig)
            iacc + (v._1 -> (oldSet + newPar))
          }
         }
        }}
      varmap.flatMap(a => {
        val l = BounderUtil.repeatingPerm(_=> a._2, 2)
        l.map(b => Edge(b.head, b(1))).toSet
      }).toSet
    }
  }
}
/**
 * Representation of a set of possible lifestate specs */
class SpecSpace(specs: Set[LSSpec]) {
  private def allI(pred:LSPred):Set[I] = pred match{
    case i@I(_,_,_) => Set(i)
    case NI(i1,i2) => Set(i1,i2)
    case And(p1,p2) => allI(p1).union(allI(p2))
    case Or(p1,p2) => allI(p1).union(allI(p2))
    case Not(p) => allI(p)
    case LSTrue => Set()
    case LSFalse => Set()
  }
  private def allI(spec:LSSpec):Set[I] = spec match{
    case LSSpec(pred, target,_) => allI(pred).union(allI(target))
  }
  private val iset: Map[(MessageType, (String, String)), I] = {
    val allISpecs = specs.flatMap(allI)
    val collected = allISpecs.groupBy(i => (i.mt, i.signatures))
    collected.flatMap{
      case (k,v) =>
        val setOfVarLists = v.map(_.lsVars)
        val maxL = setOfVarLists.foldLeft(0)((acc,v) => if(v.size > acc)v.size else acc)
        val blankVars = (0 until maxL).map(ind =>
          if(setOfVarLists.exists(l=> (l.size > ind) && !LifeState.LSAnyVal.matches(l(ind)))) "v" else "_")
        k._2.map(v => (k._1,v)->I(k._1,k._2,blankVars.toList))
    }
  }

  private var freshLSVarIndex = 0
  def nextFreshLSVar():String = {
    val ind = freshLSVarIndex
    freshLSVarIndex = freshLSVarIndex+1
    s"LS_GENERATED__${ind}"
  }
  /**
   * For step back over a place where the code may emit a message find the applicable I and assign fresh ls vars.
   * Fresh LS vars are generated for vars and constants
   * @param mt Direction of message
   * @param sig class name and method signature (e.g. void foo(java.lang.Object))
   * @return Some(I) if I exists, None otherwise.
   */
  def getIWithFreshVars(mt: MessageType, sig: (String, String)):Option[I] = {
    iset.get(mt,sig).map{i =>
      i.copy(lsVars = i.lsVars.map(a => if(a != "_") nextFreshLSVar() else "_"))
    }
  }

  /**
   * Find a lifestate spec by
   *
   * @param pkg
   * @param name
   * @return
   */
  def specsBySig(mt: MessageType, pkg:String, name:String):Set[LSSpec] = {
    // TODO: cache specs in hash map
    val specsForSig = specs.filter(a => a.target.signatures.contains((pkg,name)) && a.target.mt == mt)
    specsForSig
  }

}

