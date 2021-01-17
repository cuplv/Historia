package edu.colorado.plv.bounder.solver

import com.microsoft.z3.{BoolExpr, Context, EnumSort, Expr, FuncDecl, Solver, Sort}
import edu.colorado.plv.bounder.symbolicexecutor.state.{ClassType, SubclassOf, SuperclassOf, TypeConstraint}


/**
 * Z3 constraints that persist from state to state
 * Adds class hierarchy assertions
 * @param ctx z3 context to add class hierarchy assertions
 * @param types mapping from super types to sub types
 */
class PersistantConstraints(ctx: Context, solver: Solver, types : Map[String,Set[String]]) {
  def getSolver: Solver = solver
  def getCtx: Context = ctx

  val typeToInt: Map[String, Int] = (types.keySet + "null").zipWithIndex.toMap
  val intToType: Map[Int, String] = typeToInt.map(a => (a._2, a._1))


//  val tsort: Sort = ctx.mkFiniteDomainSort("Types", typeToInt.size)
  val tsort: EnumSort = ctx.mkEnumSort("Types", typeToInt.keys.toArray:_*)

  private def finiteDomVal(t : String):Expr = {
      tsort.getConst(typeToInt(t))
  }

  val subtypeFun: FuncDecl = ctx.mkFuncDecl("subtype", Array(tsort:Sort, tsort), ctx.mkBoolSort())

  def mkHirearchyConstraints() {
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
    solver.add(ctx.mkAnd(subtype_forall, ctx.mkNot(
      subtypeFun.apply(finiteDomVal("java.lang.Object"), finiteDomVal("null")).asInstanceOf[BoolExpr])))
  }
  mkHirearchyConstraints()
  solver.push()


  def addTypeConstraint(vname: String, typeConstraint: TypeConstraint): BoolExpr = {
    val const: Expr = ctx.mkConst("t_" + vname, tsort)
    exprTypeConstraint(const, typeConstraint)
  }

  def exprTypeConstraint(e: Expr, typeConstraint: TypeConstraint): BoolExpr = {
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
