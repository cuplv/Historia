package edu.colorado.plv.bounder

import scala.collection.mutable

object BounderUtil {
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

