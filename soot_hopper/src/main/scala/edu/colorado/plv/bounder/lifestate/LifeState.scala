package edu.colorado.plv.bounder.lifestate

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.lifestate.LifeState.LSAtom

object LifeState {
  var id = 0
  def nextLsVar():String = {
    val lsVar = "v" + id
    id = id+1
    lsVar
  }

  sealed trait LSPred {
    def lsVar: List[String]
  }
  case class AND(l1 : LSPred, l2 : LSPred) extends LSPred {
    override def lsVar: List[String] = ???
  }
  case class Not(l: LSPred) extends LSPred {
    override def lsVar: List[String] = ???
  }

  sealed trait LSAtom extends LSPred {
    def getVar(i:Int):String
    def getAtomSig:String
  }
  // A method with a signature in "signatures" has been invoed
  // lsVars:
  case class I(signatures: Set[String], lsVars : List[String]) extends LSAtom {
    override def lsVar: List[String] = lsVars

    override def getVar(i: Int): String = lsVars(i)

    override def getAtomSig: String = {
      val sortedSig = signatures.toList.sorted
      s"I(${sortedSig.mkString(":")})"
    }
  }
  // Since i1 has been invoked, i2 has not been invoked.
  case class NI(i1:I, i2:I) extends LSAtom{
    def lsVar = i1.lsVars

    override def getVar(i: Int): String = i1.lsVar(i)

    override def getAtomSig: String = s"NI(${i1.getAtomSig}, ${i2.getAtomSig})"
  }

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
     * @param atom to find predecessor aliases for
     * @return (var that can be aliased, atom that can alias)
     */
    def sliceBackStep(atom: LSAtom, index: Int) : Set[(Int, LSAtom)] = {
      val targetVar = atom.getVar(index)
      predicates.flatMap(a => {
        a.lsVar.zipWithIndex.flatMap( {case (varname, index) => if(varname == targetVar) Some(index,a) else None})
      })
    }

    /**
     * Find I predicate that matches sig
     * @param sig e.g. [CB Inv] void onCreate(Bundle)
     */
    def locateIFromMsgSig(sig: String) : Option[LSAtom] = {
      predicates.find({ case I(s,_) => s.contains(sig)})
    }

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

