package edu.colorado.plv.bounder.lifestate

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.MessageType
import edu.colorado.plv.bounder.lifestate.LifeState.LSSpec
import edu.colorado.plv.bounder.symbolicexecutor.state.PureExpr

object LifeState {
  var id = 0
  def nextLsVar():String = {
    val lsVar = "v" + id
    id = id+1
    lsVar
  }

  sealed trait LSPred {
    def lsVar: Set[String]
  }
  case class And(l1 : LSPred, l2 : LSPred) extends LSPred {
    override def lsVar: Set[String] = l1.lsVar.union(l2.lsVar)
    override def toString:String = s"(${l1.toString} AND ${l2.toString})"
  }
  case class Not(l: LSPred) extends LSPred {
    override def lsVar: Set[String] = l.lsVar
    override def toString:String = s"(NOT ${l.toString})"
  }
  case class Or(l1:LSPred, l2:LSPred) extends LSPred {
    override def lsVar: Set[String] = l1.lsVar.union(l2.lsVar)
    override def toString:String = s"(${l1.toString} OR ${l2.toString})"
  }
  case object LSTrue extends LSPred {
    override def lsVar: Set[String] = Set.empty
  }
  case object LSFalse extends LSPred {
    override def lsVar: Set[String] = Set.empty
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
      s"I_${mt.toString}_${sortedSig.head._1}_${sortedSig.head._2}"
    }
    override def toString:String = s"I($mt $identitySignature ( ${lsVars.mkString(",")} )"
  }
  // Since i1 has been invoked, i2 has not been invoked.
  case class NI(i1:I, i2:I) extends LSAtom{
    def lsVar = i1.lsVar.union(i2.lsVar)

    override def getAtomSig: String = s"NI(${i1.getAtomSig}, ${i2.getAtomSig})"

    override def identitySignature: String = s"${i1.identitySignature}_${i2.identitySignature}"
    override def toString:String = s"NI( ${i1.toString} , ${i2.toString} )"
  }
  case class LSSpec(pred:LSPred, target: I)

  // Used for abstract state
  case class LSAbsBind(modelVar:String, pureExpr: PureExpr) extends LSPred {
    override def lsVar: Set[String] = Set()
  }

  // Class that holds a graph of possible predicates and alias relations between the predicates.
  // Generated from a fast pre analysis of the applications.
  // Set of vars that can alias are represented by having the same name.
  class PredicateSpace(predicates: Set[LSAtom]){
    /** mapping from variable names to predicates containing variable */
    val findVars: Map[String, Set[LSAtom]] = predicates.foldLeft(Map[String, Set[LSAtom]]()) { (acc, v) =>
      v.lsVar.foldLeft(acc){ (iacc, varname) => iacc + (varname -> (iacc.getOrElse(varname, Set()) + v) )}
    }

    //TODO: stale back slicing function, is it still needed?
//    /**
//     *
//     * @param atom to find predecessor aliases for
//     * @return (var that can be aliased, atom that can alias)
//     */
//    def sliceBackStep(atom: LSAtom, index: Int) : Set[(Int, LSAtom)] = {
//      val targetVar = atom.getVar(index)
//      predicates.flatMap(a => {
//        a.lsVar.zipWithIndex.flatMap( {case (varname, index) => if(varname == targetVar) Some(index,a) else None})
//      })
//    }

//    /**
//     * Find I predicate that matches sig
//     * @param sig e.g. [CB Inv] void onCreate(Bundle)
//     */
//    def locateIFromMsgSig(sig: String) : Option[LSAtom] = {
//      predicates.find({ case I(_,s,_) => s.contains(sig)})
//    }

    /**
     *
     * @param src source of alias edge (index, atom sig)
     * @param tgt target of alias edge (index, atom sig)
     */
    case class Edge(src: (Int, String), tgt: (Int, String))

    def getEdgeSet(): Set[Edge] = {
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
        l.map(b => Edge(b(0), b(1))).toSet
      }).toSet
    }
  }
}
/**
 * Representation of a set of possible lifestate specs */
class SpecSpace(specs: Set[LSSpec]) {
  /**
   * Find a lifestate spec by
   * @param pkg
   * @param name
   * @return
   */
  def specsBySig(pkg:String, name:String):Set[LSSpec] = {
    // TODO: put specs in hash map or something
    specs.filter(a => a.target.signatures.contains((pkg,name)))
  }

}

