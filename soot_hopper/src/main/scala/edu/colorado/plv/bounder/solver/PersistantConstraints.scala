package edu.colorado.plv.bounder.solver

import com.microsoft.z3.{BoolExpr, Context, EnumSort, Expr, FuncDecl, Solver, Sort}
import edu.colorado.plv.bounder.solver.PersistantConstraints.primitiveTypes
import edu.colorado.plv.bounder.symbolicexecutor.state.{ClassType, SubclassOf, SuperclassOf, TypeConstraint}
import soot.ShortType

object PersistantConstraints{
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

/**
 * Z3 constraints that persist from state to state
 * Adds class hierarchy assertions
 * @param ctx z3 context to add class hierarchy assertions
 * @param types mapping from super types to sub types
 */
class PersistantConstraints(ctx: Context, solver: Solver, types : Map[String,Set[String]],
                            useZ3TypeSolver: Boolean = false) {
  def getSolver: Solver = solver
  def getCtx: Context = ctx
  def getTypes:Map[String,Set[String]] = types
  def getUseZ3TypeSolver:Boolean = useZ3TypeSolver
  def getSubtypesOf(tname:String):Set[String] = types(tname)
  def getSupertypesOf(tname:String) :Set[String] = types.keySet.filter(k => types(k).contains(tname))

  val typeToInt: Map[String, Int] = types.keySet.zipWithIndex.toMap
  val intToType: Map[Int, String] = typeToInt.map{a =>
    assert(!primitiveTypes.contains(a._1), s"Invalid class name ${a._1}")
    (a._2, a._1)}


//  val tsort: Sort = ctx.mkFiniteDomainSort("Types", typeToInt.size)
  val tsort: EnumSort = ctx.mkEnumSort("Types", typeToInt.keys.toArray:_*)

  private def finiteDomVal(t : String):Expr = {
      tsort.getConst(typeToInt(t))
  }

  val subtypeFun: FuncDecl = ctx.mkFuncDecl("subtype", Array(tsort:Sort, tsort), ctx.mkBoolSort())

  private def mkHirearchyConstraints() {
    val arg1 = ctx.mkBound(0, tsort)
    val arg2 = ctx.mkBound(1, tsort)
    val subclassConstraint =
      types.foldLeft(ctx.mkFalse: Expr)({ case (acc, (supertype, subtypes)) =>
        subtypes.foldLeft(acc) { case (acc, subtype) =>
          val conj = ctx.mkAnd(ctx.mkEq(arg1, finiteDomVal(supertype)),
            ctx.mkEq(arg2, finiteDomVal(subtype)))
          ctx.mkITE(conj, ctx.mkTrue, acc)
        }
      })

    val subtype_forall = ctx.mkForall(Array(tsort, tsort) /*sorts*/ ,
      Array(ctx.mkSymbol("arg1"), ctx.mkSymbol("arg2")) /*symbols*/ ,
      ctx.mkEq(subtypeFun.apply(arg1, arg2), subclassConstraint) /*body*/ , 1 /*weight*/ ,
      Array() /*patterns*/ , null, null, null)
    solver.add(subtype_forall)
  }
  if(useZ3TypeSolver) {
    mkHirearchyConstraints()
    solver.push()
  }


  def addTypeConstraint(vname: String, typeConstraint: TypeConstraint): BoolExpr = {
    if(!useZ3TypeSolver){
      throw new IllegalStateException("Z3 type solving disabled")
    }
    val const: Expr = ctx.mkConst("t_" + vname, tsort)
    exprTypeConstraint(const, typeConstraint)
  }

  def exprTypeConstraint(e: Expr, typeConstraint: TypeConstraint): BoolExpr = {
    if(!useZ3TypeSolver){
      throw new IllegalStateException("Z3 type solving disabled")
    }
    typeConstraint match {
      case SubclassOf(c) =>
        subtypeFun.apply(finiteDomVal(c), e).asInstanceOf[BoolExpr]
      case SuperclassOf(c) =>
        subtypeFun.apply(e, finiteDomVal(c)).asInstanceOf[BoolExpr]
      case ClassType(c) =>
        ctx.mkEq(e, finiteDomVal(c))
    }
  }
}
