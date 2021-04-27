package edu.colorado.plv.bounder.solver

import com.microsoft.z3.{BoolExpr, Context, EnumSort, Expr, FuncDecl, Solver, Sort, UninterpretedSort}
import edu.colorado.plv.bounder.ir.{AssignCmd, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, CmdWrapper, InternalMethodInvoke, InternalMethodReturn, Loc}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints.primitiveTypes
import edu.colorado.plv.bounder.symbolicexecutor.state.{ClassType, Equals, OneOfClass, PureConstraint, PureVar, State, SubclassOf, Subtype, SuperclassOf, TypeConstraint}
import org.scalactic.anyvals.NonEmptySet
import scalaz.Memo
import soot.ShortType
import upickle.default.write
import upickle.default.{macroRW, ReadWriter => RW}

import scala.collection.BitSet

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
  val primitiveTypes: List[String] = List(
    intType,
    shortType,
    byteType,
    longType,
    doubleType,
    charType,
    floatType,
    booleanType)
  val Primitive = primitiveTypes.mkString("|").r

  implicit val rw:RW[ClassHierarchyConstraints] = upickle.default.readwriter[ujson.Value].bimap[ClassHierarchyConstraints](
    x => ujson.Obj("hierarchy" -> x.getTypes, "interfaces" -> x.getInterfaces,
      "intToType" -> x.getIntToClass.map{case (k,v) => k.toString -> v}),
    json => {
      val hiearchy = json("hierarchy").obj.map{
        case (k,v) => k->v.arr.map(_.str).toSet
      }.toMap
      val interfaces = json("interfaces").arr.map(_.str).toSet
      val intToClass = json("intToType").obj.map{
        case (k,v) => k.toInt->v.str
      }
      new ClassHierarchyConstraints(hiearchy,interfaces, intToClass.toMap)
    }
  )

}

sealed trait StateTypeSolving
//case object NoTypeSolving extends StateTypeSolving //TODO: no typesolving is unsound due to subsumption
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
                                interfaces:Set[String], intToClass: Map[Int,String],
                                useZ3TypeSolver: StateTypeSolving = SolverTypeSolving ) {
  def intToString(v: Int) = intToClass(v)

  lazy val classToIntCache: Map[String, BitSet] = intToClass.groupBy{case (_,v) => v}
    .map{case (k,v) => k -> BitSet.fromSpecific(v.keySet)}
  def classToInts(clazz:String):BitSet = classToIntCache(clazz)

  def getIntToClass:Map[Int, String] = intToClass
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
  } + ("java.lang.Object" -> types.getOrElse("java.lang.Object",Set()).union(ClassHierarchyConstraints.primitiveTypes.toSet))
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
  def typeExists(tname:String):Boolean = types.contains(tname)
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
}
