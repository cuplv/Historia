package edu.colorado.plv.bounder.solver

import com.microsoft.z3.{BoolExpr, Context, EnumSort, Expr, FuncDecl, Solver, Sort, UninterpretedSort}
import edu.colorado.plv.bounder.ir.{AssignCmd, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, CmdWrapper, InternalMethodInvoke, InternalMethodReturn, Loc}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints.primitiveTypes
import edu.colorado.plv.bounder.symbolicexecutor.state.{ClassType, Equals, OneOfClass, PureConstraint, PureVar, State, SubclassOf, SuperclassOf, TypeComp, TypeConstraint}
import org.scalactic.anyvals.NonEmptySet
import scalaz.Memo
import soot.ShortType
import upickle.default.write
import upickle.default.{macroRW, ReadWriter => RW}

object ClassHierarchyConstraints{
  val intType = "int"
  val shortType = "short"
  val byteType = "byte"
  val longType = "long"
  val doubleType = "double"
  val charType = "char"
  val booleanType = "boolean"
  val floatType = "float"
  def boxedName(prim:String):String = {
    if(prim == intType) "java.lang.Integer" else{
      val capFirst = prim(0).toUpper + prim.tail
      "java.lang." + capFirst
    }
  }
  val primitiveTypes: Set[String] = Set(
    intType,
    shortType,
    byteType,
    longType,
    doubleType,
    floatType,
    booleanType)
  val Primitive = primitiveTypes.mkString("|").r

  implicit val rw:RW[ClassHierarchyConstraints] = upickle.default.readwriter[ujson.Value].bimap[ClassHierarchyConstraints](
    x => ujson.Obj("hierarchy" -> x.getTypes, "interfaces" -> x.getInterfaces),
    json => {
      val hiearchy = json("hierarchy").obj.map{
        case (k,v) => k->v.arr.map(_.str).toSet
      }.toMap
      val interfaces = json("interfaces").arr.map(_.str).toSet
      val ctx = new Context
      new ClassHierarchyConstraints(ctx, ctx.mkSolver(), hiearchy,interfaces)
    }
  )

}

sealed trait StateTypeSolving
case object NoTypeSolving extends StateTypeSolving
case object SolverTypeSolving extends StateTypeSolving
case object SetInclusionTypeSolving extends StateTypeSolving
import upickle.default.{write,read}

import upickle.default.{ReadWriter => RW, macroRW}

/**
 * Z3 constraints that persist from state to state
 * Adds class hierarchy assertions
 * @param ctx z3 context to add class hierarchy assertions
 * @param types mapping from super types to sub types
 */
class ClassHierarchyConstraints(ctx: Context, solver: Solver, types : Map[String,Set[String]],
                                interfaces:Set[String],useZ3TypeSolver: StateTypeSolving = NoTypeSolving ) {
  def getInterfaces:Set[String] = interfaces
//  def leastUpperBound(classesToGroup: Set[String]): String ={
//    if(classesToGroup.isEmpty)
//      return "java.lang.Object"
//    // Note: This is inefficient, but most classes should have a small number of super types so it may not matter
//    // This whole class should be refactored later
//    val b = getSupertypesOf(classesToGroup.head)
//    val intersectOfSuper = classesToGroup.tail.foldLeft(b){
//      case (acc, clazzToJoin) => acc.intersect(getSupertypesOf(clazzToJoin))
//    }
//    //TODO: prefer interface over class?
//    val typeWithMostSuperTypes = intersectOfSuper.reduceLeft{
//      (a,b) => if(getSupertypesOf(a).size > getSupertypesOf(b).size) a else b
//    }
//    typeWithMostSuperTypes
//  }
  def isInterface(name:String):Boolean = interfaces.contains(name)
  def getSolver: Solver = solver
  def getCtx: Context = ctx
  // Treat primitive values as subtypes of their boxed types
  val getTypes:Map[String,Set[String]] = ClassHierarchyConstraints.primitiveTypes.foldLeft(types){
    (acc,v) =>
      val boxedName = ClassHierarchyConstraints.boxedName(v)
      (acc + (v -> Set(v))) + (boxedName -> (acc.getOrElse(boxedName,Set(boxedName)) + v))
  } + ("java.lang.Object" -> types.getOrElse("java.lang.Object",Set()).union(ClassHierarchyConstraints.primitiveTypes))
  def getUseZ3TypeSolver:StateTypeSolving = useZ3TypeSolver
  def upperTypeBoundForReciever(methodReturnLoc: Loc):Option[String] = methodReturnLoc match {
    case CallinMethodInvoke(clazz, _) =>
      Some(clazz)
    case CallbackMethodInvoke(fmwClazz,_,_) =>
      Some(fmwClazz)
    case InternalMethodInvoke(clazz,_,_) =>
      Some(clazz)
    case CallinMethodReturn(clazz,_) => Some(clazz)
    case CallbackMethodReturn(fmwClazz, _, _, _) => Some(fmwClazz)
    case InternalMethodReturn(clazz, _,_) => Some(clazz)
    case _ => throw new IllegalArgumentException("Loc is not method entry/exit")
  }
  def getSubtypesOf(tname:String):Set[String] = {
    if (tname.endsWith("[]")){
      val arrayBase = tname.replaceFirst("\\[\\]","")
      getSubtypesOf(arrayBase).map(_ + "[]")
    }else {
      getTypes.getOrElse(tname,
        throw new IllegalStateException(s"Type: $tname not found"))
    }
  }

  //  def getSupertypesOf(tname:String) :Set[String] = types.keySet.filter(k => types(k).contains(tname))

  def iGetSupertypesOf(tname:String):Set[String] = {
    if (tname.endsWith("[]")){
      val arrayBase = tname.replaceFirst("\\[\\]","")
      iGetSupertypesOf(arrayBase).map(_ + "[]")
    }else {
      getTypes.keySet.filter(k => getTypes(k).contains(tname))
    }
  }
  val getSupertypesOf : String => Set[String] = Memo.mutableHashMapMemo{ iGetSupertypesOf }

  val tsort: UninterpretedSort = ctx.mkUninterpretedSort("ClassTypes")
  val typeToSolverConst: Map[String, Expr] = getTypes.keySet.map(t => (t-> ctx.mkConst(s"type_$t", tsort))).toMap

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
        val solverTypes = getTypes(c).map(typeToSolverConst).toArray
        equalToOneOf(e, solverTypes)
      case SuperclassOf(c) =>
        val solverTypes = getTypes.keySet.filter(k => getTypes(k).contains(c)).map(typeToSolverConst)
        equalToOneOf(e, solverTypes.toArray)
      case ClassType(c) =>
        ctx.mkEq(e, solverValueOfType(c))
    }
  }

  //def typeSetForPureVar(v:PureVar, state:State):Set[String] = {
  //  def typeSet(const: PureConstraint):Set[String] = const match{
  //    case PureConstraint(_, TypeComp, SuperclassOf(c)) => getSupertypesOf(c)
  //    case PureConstraint(_, TypeComp, SubclassOf(c)) => getSubtypesOf(c)
  //    case PureConstraint(_, TypeComp, ClassType(c)) => Set(c)
  //    case PureConstraint(_, TypeComp, OneOfClass(c)) => c.flatMap(getSubtypesOf)
  //    case _ => Set()
  //  }
  //  state.pureFormula.foldLeft(None:Option[Set[String]]){
  //    case (None,p@PureConstraint(p2, TypeComp, _)) if p2 == v =>
  //      Some(typeSet(p))
  //    case (Some(acc),p@PureConstraint(p2, TypeComp, _)) if p2 == v =>
  //      Some(acc.intersect(typeSet(p)))
  //    case (acc,_) =>
  //      acc
  //  }.getOrElse(getSubtypesOf("java.lang.Object"))
  //}
  //def pureVarTypeMap(state:State):Map[PureVar, Set[String]] = {
  //  val pvMap: Map[PureVar, Set[String]] =
  //    state.pureVars().map(p => (p,typeSetForPureVar(p,state))).toMap
  //  val pvMap2 = state.pureFormula.foldLeft(pvMap){
  //    case(acc, PureConstraint(p1:PureVar, Equals, p2:PureVar)) => {
  //      val newPvClasses = acc(p1).intersect(acc(p2))
  //      acc + (p1->newPvClasses) + (p2 -> newPvClasses)
  //    }
  //    case (acc,_) => acc
  //  }
  //  pvMap2
  //}
}
