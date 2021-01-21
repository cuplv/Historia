package edu.colorado.plv.bounder.lifestate

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.MessageType
import edu.colorado.plv.bounder.lifestate.LifeState.{And, I, LSFalse, LSPred, LSSpec, LSTrue, NI, Not, Or}
import edu.colorado.plv.bounder.symbolicexecutor.state.PureExpr

object LifeState {
  var id = 0
  def nextLsVar():String = {
    val lsVar = "v" + id
    id = id+1
    lsVar
  }

  sealed trait LSPred {
    def contains(mt:MessageType,sig: (String, String)):Boolean

    def lsVar: Set[String]
  }
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
    override def contains(mt:MessageType,sig: (String, String)): Boolean = l2.contains(mt, sig) || l2.contains(mt,sig)
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

  // A method with a signature in "signatures" has been invoed
  // lsVars: element 0 is return value, element 1 is reciever, rest of the elements are arguemnts
  // A string of "_" means "don't care"
  // primitives are parsed as in java "null", "true", "false", numbers etc.
  case class I(mt: MessageType, signatures: Set[(String, String)], lsVars : List[String]) extends LSAtom {
    private val sortedSig = signatures.toList.sorted
    override def lsVar: Set[String] = lsVars.filter(_!="_").toSet

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
  // Since i1 has been invoked, i2 has not been invoked.
  case class NI(i1:I, i2:I) extends LSAtom{
    def lsVar: Set[String] = i1.lsVar.union(i2.lsVar)

    override def getAtomSig: String = s"NI(${i1.getAtomSig}, ${i2.getAtomSig})"

    override def identitySignature: String = s"${i1.identitySignature}_${i2.identitySignature}"
    override def toString:String = s"NI( ${i1.toString} , ${i2.toString} )"

    override def contains(mt:MessageType,sig: (String, String)): Boolean = i1.contains(mt, sig) || i2.contains(mt, sig)
  }
  case class LSSpec(pred:LSPred, target: I)

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
    case LSSpec(pred, target) => allI(pred).union(allI(target))
  }
  val iset: Map[(MessageType, (String, String)), I] =
    specs.flatMap(allI).flatMap(i => i.signatures.map(j => ((i.mt,j),i))).toMap
  private var freshLSVarIndex = 0
  def nextFreshLSVar():String = {
    val ind = freshLSVarIndex
    freshLSVarIndex = freshLSVarIndex+1
    s"LS_GENERATED__${ind}"
  }
  /**
   * For step back over a place where the code may emit a message find the applicable I and assign fresh ls vars.
   * @param mt
   * @param sig
   * @return Some(I) if I exists, None otherwise
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
  def specsBySig(mt: MessageType, pkg:String, name:String):Option[LSSpec] = {
    // TODO: cache specs in hash map
    val specsForSig = specs.filter(a => a.target.signatures.contains((pkg,name)) && a.target.mt == mt)
    assert(specsForSig.size < 2, "Spec is not well formed, multiple applicable specs for transfer")
    specsForSig.headOption
  }

}

