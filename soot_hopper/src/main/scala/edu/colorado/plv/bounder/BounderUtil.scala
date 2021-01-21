package edu.colorado.plv.bounder

import edu.colorado.plv.bounder.symbolicexecutor.state.{BottomQry, PathNode, SomeQry, WitnessedQry}

import scala.collection.mutable

object BounderUtil {
  trait ResultSummary
  case object Proven extends ResultSummary
  case object Witnessed extends ResultSummary
  case object Timeout extends ResultSummary
  def interpretResult(result: Set[PathNode]):ResultSummary = {
    if(result.forall {
      case PathNode(_: BottomQry, _, _) => true
      case PathNode(_: WitnessedQry, _, _) => false
      case PathNode(_: SomeQry, _, Some(_)) => true
      case PathNode(_: SomeQry, _, _) => false
    }) Proven
    else if(result.exists{
      case PathNode(_: WitnessedQry, _, _) => true
      case _ => false
    }) Witnessed
    else Timeout
  }

  def repeatingPerm[T](elems:Int=>Iterable[T], genSize: Int): Iterable[List[T]] = {
    val acc = mutable.ListBuffer[List[T]]()
    def repeatingPermRec(elems: Int=>Iterable[T], depth: Int, partResult: List[T]): Unit = depth match {
      case 0 => acc.addOne(List())
      case 1 => for (elem <- elems(0)) acc.addOne(elem :: partResult)
      case n => for (elem <- elems(n-1))
        repeatingPermRec(elems, depth - 1, elem :: partResult)
    }
    if (genSize < 0) throw new IllegalArgumentException("Negative lengths not allowed in repeatingPerm...")
    repeatingPermRec(elems, genSize, Nil)
    acc
  }
}

