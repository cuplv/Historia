package edu.colorado.plv.bounder.solver

import edu.colorado.plv.bounder.ir.{CBEnter, FwkMethod, TMessage}
import edu.colorado.plv.bounder.lifestate.LifeState.{Once, SubClassMatcher}
import edu.colorado.plv.bounder.symbolicexecutor.state.{NPureVar, NamedPureVar, PureExpr, PureVal, PureVar, TAddr, TVal}
import org.scalatest.Outcome
import org.scalatest.funsuite.AnyFunSuite

class EncodingToolsTest extends AnyFunSuite{
  implicit val cha = new ClassHierarchyConstraints(
    Map("foo"->Set("foo"), "bar"->Set("bar")),
    Set(), Map(1->"foo"))

  def bodgePv(v:Any):PureExpr = v match{
    case v:String => NamedPureVar(v)
    case n:Int => NPureVar(n)
    case v:PureVal => v
    case v:PureVar => v
  }

  def bodgeTraceV(v:Any):TVal = v match {
    case i:Int => TAddr(i)
    case v:TVal => v
    case _ => ???
  }
  def mkOnce(name:String, vars:List[Any]) =
    Once(CBEnter, SubClassMatcher(Set(""), name,name),vars.map(bodgePv))
  def mkTMsg(name:String, args:List[Any]) = TMessage(CBEnter, FwkMethod(name, ""), args.map(bodgeTraceV))

  val x = bodgePv("x")
  val y = bodgePv("y")

  val pv0 = NPureVar(0)


  // matchers
  val oFoo_x_y = mkOnce("foo", x::y::Nil)
  val oBar_x_y = mkOnce("bar", x::y::Nil)

  // trace elements
  val foo_1_2 = mkTMsg("foo",1::2::Nil)

  test("Encoded O foo(x,y) matches foo(@1,@2)"){
    val trace = List(foo_1_2)

    val (oFoo_regm,_) = EncodingTools.predToRM(oFoo_x_y,pv0)

    assert(oFoo_regm.containsTrace(List.empty).isEmpty)
    assert(oFoo_regm.containsTrace(trace).nonEmpty)

  }
}
