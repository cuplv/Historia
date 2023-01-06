package edu.colorado.plv.bounder.solver

import edu.colorado.plv.bounder.ir.{CBEnter, CallbackMethodReturn, FwkMethod, TMessage}
import edu.colorado.plv.bounder.lifestate.LifeState.{AbsMsg, And, Exists, Forall, LSConstraint, Not, Or, Signature, SubClassMatcher}
import edu.colorado.plv.bounder.symbolicexecutor.state.{CallStackFrame, ConcreteAddr, ConcreteVal, Equals, NPureVar, NamedPureVar, NotEquals, PureConstraint, PureExpr, PureVal, PureVar, StackVar, State, StateFormula}
import edu.colorado.plv.bounder.synthesis.SynthTestUtil.{dummyLoc, dummyMethod, intToClass}
import org.scalatest.Outcome
import org.scalatest.funsuite.AnyFunSuite

class EncodingToolsTest extends AnyFunSuite{
  implicit val cha = new ClassHierarchyConstraints(
    Map("foo"->Set("foo"), "bar"->Set("bar")),
    Set(), Map(1->"foo"))

  private def getZ3StateSolver():
  (Z3StateSolver, ClassHierarchyConstraints) = {
//    val pc = new ClassHierarchyConstraints(cha, Set("java.lang.Runnable"), intToClass)
    (new Z3StateSolver(cha, timeout = 20000, defaultOnSubsumptionTimeout = (z3SolverCtx: Z3SolverCtx) => {
      println(z3SolverCtx)
      throw new IllegalStateException("Exceeded time limit for test")
    }, pushSatCheck = true), cha)
  }

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
  val pv1 = NPureVar(1)
  val pv2 = NPureVar(2)



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
    val pred = And(Forall(x::Nil,Or(Not(oBar_x_y), LSConstraint.mk(x,Equals,y))), Exists(x::Nil, oFoo_x_y))
    val res = EncodingTools.prenexNormalForm(pred)
    val (solver,_) = getZ3StateSolver
    assert(solver.canSubsume(pred,res))
    assert(solver.canSubsume(res,pred))
  }
  test("Convert LSPred to CNF"){
    val pred = Or(Forall(x::Nil,And(Not(oBar_x_y), LSConstraint.mk(x,Equals,y))), Exists(x::Nil, oFoo_x_y))
    val res = EncodingTools.toCNF(pred)

    val (solver,_) = getZ3StateSolver
    assert(solver.canSubsume(pred,res))
    assert(solver.canSubsume(res,pred))
    println(res)
  }
  test("reduce state pure vars"){
    val top = State.topState

    val s1 = top.addPureConstraint(PureConstraint(pv1, Equals, pv2))
    s1.setSimplified()
    val redS1 = EncodingTools.reduceStatePureVars(s1)
    assert(redS1.get.sf.pureFormula.isEmpty)

    val s2 = s1.copy(sf = s1.sf.copy(callStack =
      CallStackFrame(
        CallbackMethodReturn(Signature("foo","foo()"), dummyMethod, None), None, Map(StackVar("x")-> pv1))::Nil))

    def withLocal(state: State, name: String, tgt: PureExpr): State = {
      val stackHead = state.sf.callStack.head
      val newCallStack = stackHead.copy(locals = stackHead.locals + (StackVar(name) -> tgt))
      state.copy(sf = state.sf.copy(newCallStack::state.sf.callStack.tail))
    }
    s2.setSimplified()
    val redS2 = EncodingTools.reduceStatePureVars(s2)
    assert(redS2.get.sf.pureFormula.isEmpty)

    val s3 = withLocal(withLocal(s2,"z",pv2),"y",pv0)
      .addPureConstraint(PureConstraint(pv0, NotEquals,pv2))
    s3.setSimplified()
    val redS3 = EncodingTools.reduceStatePureVars(s3)
    assert(redS3.get.sf.pureFormula.size == 1)

  }
}
