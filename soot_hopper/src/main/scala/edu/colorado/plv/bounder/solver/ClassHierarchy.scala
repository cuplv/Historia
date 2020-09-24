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
class ClassHierarchy(ctx: Context, solver: Solver, types : List[(String,String)]) {

  val typeToInt: Map[String, Int] = types.flatMap(a => List(a._1, a._2)).toSet.zipWithIndex.toMap
  val intToType: Map[Int, String] = typeToInt.map(a => (a._2, a._1))

  val tsort: Sort = ctx.mkFiniteDomainSort("Types", typeToInt.size)


  private def finiteDomVal(t : String):Expr = {
    ctx.mkNumeral(typeToInt(t), tsort)
  }
  def mkHirearchyConstraints() {
    // Direct subclass function
    val subtypeFun: FuncDecl = ctx.mkFuncDecl("directsubtype", Array(tsort, tsort), ctx.mkBoolSort())
   //   ctx.mkFreshFuncDecl("directsubtype", Array(tsort, tsort), ctx.mkBoolSort)

    val arg1 = ctx.mkBound(0, tsort)
    val arg2 = ctx.mkBound(1, tsort)
    val subclassConstraint =
      types.foldLeft(ctx.mkFalse: Expr)({ case (acc, (supertype, subtype)) =>
        val conj = ctx.mkAnd(ctx.mkEq(arg1, finiteDomVal(supertype)),
          ctx.mkEq(arg2, finiteDomVal(subtype)))
        ctx.mkITE(conj, ctx.mkTrue, acc)
      })

    val subtype_forall = ctx.mkForall(Array(tsort, tsort) /*sorts*/ ,
      Array(ctx.mkSymbol("arg1"), ctx.mkSymbol("arg2")) /*symbols*/ ,
      ctx.mkEq(subtypeFun.apply(arg1, arg2), subclassConstraint) /*body*/ , 1 /*weight*/ ,
      Array() /*patterns*/ , null, null, null)
    solver.add(subtype_forall)

    // Transitive subclass function
    val tS:FuncDecl = ctx.mkFuncDecl("subtype", Array(tsort, tsort), ctx.mkBoolSort())

    val ta1 = ctx.mkBound(0, tsort)
    val ta2 = ctx.mkBound(1, tsort)
    val ta3 = ctx.mkBound(2, tsort)
    val exists = ctx.mkExists(Array(tsort), Array(ctx.mkSymbol("ta3")),
      ctx.mkAnd(ctx.mkEq(subtypeFun.apply(ta1, ta3), ctx.mkTrue),
        ctx.mkEq(tS.apply(ta3, ta2), ctx.mkTrue)), 1, Array(), null, null, null )
    val allT = ctx.mkForall(Array(tsort, tsort), Array(ctx.mkSymbol("ta1"), ctx.mkSymbol("ta2")),
      ctx.mkEq(tS.apply(ta1, ta2), ctx.mkOr(ctx.mkEq(subtypeFun.apply(ta1, ta2), ctx.mkTrue), exists))/*body*/,
      1, Array(), null, null, null)
    solver.add(allT)

    // It doesn't seem I can connect directsubtype like this
    //ctx.mkForall(Array(tsort, tsort, tsort)/*sorts*/,
    //  Array(ctx.mkSymbol("ta1"), ctx.mkSymbol("ta2"), ctx.mkSymbol("ta3"))/*symbols*/,
    //  ctx.mkImplies(
    //    ctx.mkAnd(ctx.mkEq(tS.apply(ta1,ta2), ctx.mkTrue()),ctx.mkEq(tS.apply(ta2,ta3),
    //      ctx.mkTrue())),ctx.mkEq(tS.apply(ta1, ta3), ctx.mkTrue)) /*body*/
    //  , 1, Array(), null, null, null)

  }
  mkHirearchyConstraints()
  solver.push()


  def addTypeConstraint(vname: String, typeConstraint: TypeConstraint) = ???
}
