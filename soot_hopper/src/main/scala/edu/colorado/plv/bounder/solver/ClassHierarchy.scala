package edu.colorado.plv.bounder.solver

import com.microsoft.z3.{Context, Expr, FiniteDomainSort, FuncDecl, IntSort, Native, Solver, Sort}

sealed trait TypeConstraint
case class SubclassOf(clazz: String) extends TypeConstraint
case class SuperclassOf(clazz:String) extends TypeConstraint

/**
 * Adds class hierarchy assertions
 * @param ctx z3 context to add class hierarchy assertions
 * @param types mapping from super types to sub types
 */
class ClassHierarchy(ctx: Context, solver: Solver, types : Map[String,Set[String]]) {

  val typeToInt: Map[String, Int] = types.keySet.zipWithIndex.toMap
  val intToType: Map[Int, String] = typeToInt.map(a => (a._2, a._1))


  val tsort: Sort = ctx.mkFiniteDomainSort("Types", typeToInt.size)

  private def finiteDomVal(t : String):Expr = {
    ctx.mkNumeral(typeToInt(t), tsort)
  }
  val subtypeFun: FuncDecl = ctx.mkFuncDecl("subtype", Array(tsort, tsort), ctx.mkBoolSort())
  def mkHirearchyConstraints() {
    // Direct subclass function
   //   ctx.mkFreshFuncDecl("directsubtype", Array(tsort, tsort), ctx.mkBoolSort)

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
  mkHirearchyConstraints()
  solver.push()


  def addTypeConstraint(vname: String, typeConstraint: TypeConstraint) = {
    val const = ctx.mkConst(vname, tsort)
    typeConstraint match {
      case SubclassOf(c) =>
        solver.add(ctx.mkEq(subtypeFun.apply(finiteDomVal(c), const), ctx.mkTrue))
      case SuperclassOf(c) =>
        solver.add(ctx.mkEq(subtypeFun.apply(const, finiteDomVal(c)), ctx.mkTrue))
    }
  }
}
