package edu.colorado.plv.bounder.solver

import edu.colorado.plv.bounder.ir.{CBEnter, FwkMethod, TMessage}
import edu.colorado.plv.bounder.lifestate.LifeState.{AbsMsg, And, Exists, Signature, SubClassMatcher}
import edu.colorado.plv.bounder.symbolicexecutor.state.{ConcreteAddr, ConcreteVal, NPureVar, NamedPureVar, PureExpr, PureVal, PureVar}
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

  def bodgeTraceV(v:Any):ConcreteVal = v match {
    case i:Int => ConcreteAddr(i)
    case v:ConcreteVal => v
    case _ => ???
  }
  def mkOnce(name:String, vars:List[Any]) =
    AbsMsg(CBEnter, SubClassMatcher(Set(""), name,name),vars.map(bodgePv))
  def mkTMsg(name:String, args:List[Any]) = TMessage(CBEnter, FwkMethod(Signature("",name)), args.map(bodgeTraceV))

  val x = NamedPureVar("x")
  val y = NamedPureVar("y")
  val a = NamedPureVar("a")
  val b = NamedPureVar("b")

  val pv0 = NPureVar(0)


  // matchers
  val oFoo_x_y = mkOnce("foo", x::y::Nil)
  val oFoo_a_a = mkOnce("foo", a::b::Nil)
  val oBar_x_y = mkOnce("bar", x::y::Nil)

  // trace elements
  val foo_1_2 = mkTMsg("foo()",1::2::Nil)

  ignore("Encoded O foo(x,y) matches foo(@1,@2)"){
    //TODO: register machine not used for anything yet, un-ignore this test if we start using it
    val trace = List(foo_1_2)

    val (oFoo_regm,_) = EncodingTools.predToRM(oFoo_x_y,pv0)

    assert(oFoo_regm.containsTrace(List.empty).isEmpty)
    assert(oFoo_regm.containsTrace(trace).nonEmpty)
  }

  test("Lift quantifiers from temporal formula"){
    val pred = And(oFoo_x_y, Exists(x::Nil, oFoo_x_y))
  }
}
