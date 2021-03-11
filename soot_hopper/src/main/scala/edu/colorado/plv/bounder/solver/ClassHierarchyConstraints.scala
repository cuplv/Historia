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
      new ClassHierarchyConstraints(hiearchy,interfaces)
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
 * @param types mapping from super types to sub types
 */
class ClassHierarchyConstraints(types : Map[String,Set[String]],
                                interfaces:Set[String],useZ3TypeSolver: StateTypeSolving = SetInclusionTypeSolving ) {
  def getInterfaces:Set[String] = interfaces
  def intersectUpper(t1:String, t2:String):Set[String] = {
    if(types(t1).contains(t2))
      Set(t2)
    else if(types(t2).contains(t1))
      Set(t1)
    else
      types(t1).intersect(types(t2))
  }

  def isInterface(name:String):Boolean = interfaces.contains(name)
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

  //TODO: move to solver
//  val tsort: UninterpretedSort = ctx.mkUninterpretedSort("ClassTypes")
//  val typeToSolverConst: Map[String, Expr] = getTypes.keySet.map(t => (t-> ctx.mkConst(s"type_$t", tsort))).toMap
//
//  private def solverValueOfType(t : String):Expr = {
//    typeToSolverConst(t)
//  }

//  private def mkHirearchyConstraints() {
//    solver.add(ctx.mkDistinct(typeToSolverConst.map{case (_,v) => v}.toArray:_*))
//  }
//  if(useZ3TypeSolver == SolverTypeSolving) {
//    mkHirearchyConstraints()
//    solver.push()
//  }
//
//
//  def addTypeConstraint(vname: String, typeConstraint: TypeConstraint): BoolExpr = {
//    if(useZ3TypeSolver != SolverTypeSolving){
//      throw new IllegalStateException("Z3 type solving disabled")
//    }
//    val const: Expr = ctx.mkConst("t_" + vname, tsort)
//    exprTypeConstraint(const, typeConstraint)
//  }
//
//  private def equalToOneOf(e : Expr, vals : Array[Expr]):BoolExpr = {
//    if(useZ3TypeSolver != SolverTypeSolving){
//      throw new IllegalStateException("Z3 type solving disabled")
//    }
//    ctx.mkOr(vals.map(v => ctx.mkEq(e,v)):_*)
//  }
//  def equalToOneOfTypes(e: Expr, types: Set[String]):BoolExpr = {
//    if(useZ3TypeSolver != SolverTypeSolving){
//      throw new IllegalStateException("Z3 type solving disabled")
//    }
//    val solverTypes = types.map(solverValueOfType)
//    equalToOneOf(e,solverTypes.toArray)
//  }
//  def exprTypeConstraint(e: Expr, typeConstraint: TypeConstraint): BoolExpr = {
//    if(useZ3TypeSolver != SolverTypeSolving){
//      throw new IllegalStateException("Z3 type solving disabled")
//    }
//    typeConstraint match {
//      case SubclassOf(c) =>
//        val solverTypes = getTypes(c).map(typeToSolverConst).toArray
//        equalToOneOf(e, solverTypes)
//      case SuperclassOf(c) =>
//        val solverTypes = getTypes.keySet.filter(k => getTypes(k).contains(c)).map(typeToSolverConst)
//        equalToOneOf(e, solverTypes.toArray)
//      case ClassType(c) =>
//        ctx.mkEq(e, solverValueOfType(c))
//    }
//  }

}
