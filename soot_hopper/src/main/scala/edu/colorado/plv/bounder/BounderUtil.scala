package edu.colorado.plv.bounder

import edu.colorado.plv.bounder.ir.{AppLoc, CallbackMethodInvoke, CallbackMethodReturn, InternalMethodInvoke, InternalMethodReturn, Loc}
import edu.colorado.plv.bounder.symbolicexecutor.{AppCodeResolver, SymbolicExecutorConfig}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BottomQry, IPathNode, PathNode, SomeQry, WitnessedQry}

import scala.annotation.tailrec
import scala.collection.mutable

object BounderUtil {
  trait ResultSummary
  case object Proven extends ResultSummary
  case object Witnessed extends ResultSummary
  case object Timeout extends ResultSummary
  case object Unreachable extends ResultSummary
  def interpretResult(result: Set[IPathNode]):ResultSummary = {
    if(result.forall {
      case PathNode(_: BottomQry, _) => true
      case PathNode(_: WitnessedQry, _) => false
      case PathNode(_: SomeQry, true) => true
      case PathNode(_: SomeQry, false) => false
    }) if(result.size > 0) Proven else Unreachable
    else if(result.exists{
      case PathNode(_: WitnessedQry, _) => true
      case _ => false
    }) Witnessed
    else Timeout
  }

  def allMap[T](n1:Set[T], n2:Set[T]):List[Map[T,T]] = {
    if(n1.isEmpty){
      List(n2.map(n => n->n).toMap)
    }else if(n2.isEmpty){
      List(n1.map(n => n->n).toMap)
    }else{
      val h = n1.head
      n2.flatMap{tgt =>
        allMap(n1.tail,n2 - tgt).map( v => v + (h -> tgt))
      }.toList
    }
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

  // Abstract interpretation with no widen
  def graphFixpoint[N,V](start: Set[N],
                         startVal: V,
                         botVal: V,
                         next: N=>Set[N],
                         comp: (V,N) => V,
                         join: (V,V)=>V ): Map[N,V] = {
    // computed : map from nodes to their outputs
    val initialComp = start.map( a=>(a -> comp(startVal,a))).toMap

    @tailrec
    def iGraphFixpoint(toVisit:Set[N], computed:Map[N,V]) :Map[N,V] = {
      if(toVisit.isEmpty) {
        computed
      } else{
        val c = toVisit.head
        val preV = computed(c)
        val nextNodes = next(c)
        val (addTo, newComp) = nextNodes.foldLeft((List[N](),computed)){
          case ((nextVisit, computed_),cNode) =>
            val oldNextV = computed_.getOrElse(cNode,botVal)
            val newNextV = comp(preV, cNode)
            val joined = join(oldNextV,newNextV)
            val nextVisit2 = if(computed_.contains(cNode) && oldNextV == joined)
              nextVisit else cNode::nextVisit
            (nextVisit2, computed_ + (cNode -> joined))
        }
        iGraphFixpoint(toVisit.tail ++ addTo, newComp)
      }
    }
    iGraphFixpoint(start, initialComp)
  }

  def graphExists[N](start: Set[N],
                       next: N=>Set[N],
                       exists: N=>Boolean
                      ):Boolean = {
    @tailrec
    def iGraphExists(toVisit: Set[N], visited: Set[N]):Boolean = {
      if(toVisit.isEmpty)
        return false
      val c = toVisit.head
      if(exists(c)){
        true
      }else{
        val nextV = next(c) -- visited
        iGraphExists(toVisit.tail.union(nextV), visited + c)
      }
    }
    iGraphExists(start, Set())
  }

  def resolveMethodEntryForAppLoc(resolver : AppCodeResolver, appLoc: AppLoc) :List[Loc]= {
    resolver.resolveCallbackEntry(appLoc.method) match {
      case Some(CallbackMethodInvoke(clazz, name, loc)) =>
        CallbackMethodInvoke(clazz, name, loc)::
          InternalMethodInvoke(appLoc.method.classType, appLoc.method.simpleName, appLoc.method)::Nil
      case None => {
        InternalMethodInvoke(appLoc.method.classType, appLoc.method.simpleName, appLoc.method)::Nil
      }
      case _ =>
        throw new IllegalArgumentException
    }
  }
  def resolveMethodReturnForAppLoc(resolver : AppCodeResolver, appLoc: AppLoc) :List[Loc]= {
    resolver.resolveCallbackEntry(appLoc.method) match {
      case Some(CallbackMethodInvoke(clazz, name, loc)) =>
        CallbackMethodReturn(clazz, name, loc, None)::
          InternalMethodReturn(appLoc.method.classType, appLoc.method.simpleName, appLoc.method)::Nil
      case None => {
        InternalMethodReturn(appLoc.method.classType, appLoc.method.simpleName, appLoc.method)::Nil
      }
      case _ =>
        throw new IllegalArgumentException
    }
  }
}

/**
 * import OptionPickler._ to replace json null/nonnull with Some/None
 */
object OptionPickler extends upickle.AttributeTagged {
  override implicit def OptionWriter[T: Writer]: Writer[Option[T]] =
    implicitly[Writer[T]].comap[Option[T]] {
      case None => null.asInstanceOf[T]
      case Some(x) => x
    }

  override implicit def OptionReader[T: Reader]: Reader[Option[T]] =
    new Reader.Delegate[Any, Option[T]](implicitly[Reader[T]].map(Some(_))){
      override def visitNull(index: Int) = None
    }
}