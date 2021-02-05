package edu.colorado.plv.bounder.solver

import com.microsoft.z3.{BoolExpr, Context, EnumSort, Expr, FuncDecl, Solver, Sort, UninterpretedSort}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints.primitiveTypes
import edu.colorado.plv.bounder.symbolicexecutor.state.{ClassType, Equals, PureConstraint, PureVar, State, SubclassOf, SuperclassOf, TypeComp, TypeConstraint}
import scalaz.Memo
import soot.ShortType

object ClassHierarchyConstraints{
  val intType = "int"
  val shortType = "short"
  val byteType = "byte"
  val longType = "long"
  val doubleType = "double"
  val charType = "char"
  val booleanType = "boolean"
  val floatType = "float"
  val primitiveTypes: Set[String] = Set(
    intType,
    shortType,
    byteType,
    longType,
    doubleType,
    floatType,
    booleanType)
  val Primitive = primitiveTypes.mkString("|").r
}

sealed trait StateTypeSolving
case object NoTypeSolving extends StateTypeSolving
case object SolverTypeSolving extends StateTypeSolving
case object SetInclusionTypeSolving extends StateTypeSolving
/**
 * Z3 constraints that persist from state to state
 * Adds class hierarchy assertions
 * @param ctx z3 context to add class hierarchy assertions
 * @param types mapping from super types to sub types
 */
class ClassHierarchyConstraints(ctx: Context, solver: Solver, types : Map[String,Set[String]],
                                useZ3TypeSolver: StateTypeSolving = NoTypeSolving ) {
  def getSolver: Solver = solver
  def getCtx: Context = ctx
  def getTypes:Map[String,Set[String]] = types
  def getUseZ3TypeSolver:StateTypeSolving = useZ3TypeSolver
  def getSubtypesOf(tname:String):Set[String] = types(tname)
//  def getSupertypesOf(tname:String) :Set[String] = types.keySet.filter(k => types(k).contains(tname))

  val getSupertypesOf : String => Set[String] = Memo.mutableHashMapMemo{ tname =>
    types.keySet.filter(k => types(k).contains(tname))
  }

  val tsort: UninterpretedSort = ctx.mkUninterpretedSort("ClassTypes")
  val typeToSolverConst: Map[String, Expr] = types.keySet.map(t => (t-> ctx.mkConst(s"type_$t", tsort))).toMap

  private def solverValueOfType(t : String):Expr = {
    typeToSolverConst(t)
  }

  private def mkHirearchyConstraints() {
    solver.add(ctx.mkDistinct(typeToSolverConst.map{case (_,v) => v}.toArray:_*))
  }
  if(useZ3TypeSolver == SolverTypeSolving) {
    mkHirearchyConstraints()
    solver.push()
  }


  def addTypeConstraint(vname: String, typeConstraint: TypeConstraint): BoolExpr = {
    if(useZ3TypeSolver != SolverTypeSolving){
      throw new IllegalStateException("Z3 type solving disabled")
    }
    val const: Expr = ctx.mkConst("t_" + vname, tsort)
    exprTypeConstraint(const, typeConstraint)
  }

  private def equalToOneOf(e : Expr, vals : Array[Expr]):BoolExpr = {
    if(useZ3TypeSolver != SolverTypeSolving){
      throw new IllegalStateException("Z3 type solving disabled")
    }
    ctx.mkOr(vals.map(v => ctx.mkEq(e,v)):_*)
  }
  def equalToOneOfTypes(e: Expr, types: Set[String]):BoolExpr = {
    if(useZ3TypeSolver != SolverTypeSolving){
      throw new IllegalStateException("Z3 type solving disabled")
    }
    val solverTypes = types.map(solverValueOfType)
    equalToOneOf(e,solverTypes.toArray)
  }
  def exprTypeConstraint(e: Expr, typeConstraint: TypeConstraint): BoolExpr = {
    if(useZ3TypeSolver != SolverTypeSolving){
      throw new IllegalStateException("Z3 type solving disabled")
    }
    typeConstraint match {
      case SubclassOf(c) =>
        val solverTypes = types(c).map(typeToSolverConst).toArray
        equalToOneOf(e, solverTypes)
      case SuperclassOf(c) =>
        val solverTypes = types.keySet.filter(k => types(k).contains(c)).map(typeToSolverConst)
        equalToOneOf(e, solverTypes.toArray)
      case ClassType(c) =>
        ctx.mkEq(e, solverValueOfType(c))
    }
  }

  def typeSetForPureVar(v:PureVar, state:State):Set[String] = {
    state.pureFormula.foldLeft(getSubtypesOf("java.lang.Object")) {
      case (acc, PureConstraint(p2, TypeComp, SubclassOf(c))) if v == p2 => acc.intersect(getSubtypesOf(c))
      case (acc, PureConstraint(p2, TypeComp, ClassType(c))) if v == p2 => acc.intersect(Set(c))
      case (acc, PureConstraint(p2, TypeComp, SuperclassOf(c))) if v == p2 => acc.intersect(getSupertypesOf(c))
      case (acc, _) => acc
    }
  }
  def pureVarTypeMap(state:State):Map[PureVar, Set[String]] = {
    val pvMap: Map[PureVar, Set[String]] = state.pureVars().map(p => (p,typeSetForPureVar(p,state))).toMap
    val pvMap2 = state.pureFormula.foldLeft(pvMap){
      case(acc, PureConstraint(p1:PureVar, Equals, p2:PureVar)) => {
        val newPvClasses = acc(p1).intersect(acc(p2))
        acc + (p1->newPvClasses) + (p2 -> newPvClasses)
      }
      case (acc,_) => acc
    }
    pvMap2
  }
}
