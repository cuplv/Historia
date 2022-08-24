package edu.colorado.plv.bounder.lifestate

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{CBEnter, CBExit, CIEnter, CIExit, MessageType}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, CLInit, Exists, Forall, FreshRef, LSConstraint, LSFalse, LSImplies, LSPred, LSSpec, LSTrue, NS, Not, Once, Or, UComb}
import edu.colorado.plv.bounder.solver.EncodingTools.Assign
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, EncodingTools}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BoolVal, ClassVal, CmpOp, Equals, NamedPureVar, NotEquals, NullVal, PureExpr, PureVal, PureVar, State, TVal, TopVal, TypeComp}

import scala.util.parsing.combinator._
import upickle.default.{macroRW, ReadWriter => RW}

import scala.util.matching.Regex

//object LSVarGen{
//  private var next = 0

//  def setNext(states:List[State]):Unit = {
//
//    states.foreach{s =>
//      val mv = s.sf.traceAbstraction.modelVars.keySet ++ s.sf.traceAbstraction.rightOfArrow.flatMap {
//        case CLInit(sig) => Set()
//        case FreshRef(v) => Set(v)
//        case Once(mt, signatures, lsVars) => lsVars
//      }
//      mv.map{
//        case n if n.startsWith("LS__") && n.drop(4).toInt >= next =>
//          next = n.drop(4).toInt
//        case _ =>
//      }
//    }
//  }
//  def getNext:String = {
//    next = next + 1
//    s"LS__${next}"
//  }
//}

object LSExpParser {
  val LSNullConstReg = "@(?:null|Null|NULL)".r
  val LSBoolConstReg = "@(false|true|False|True)".r
  val LSVarReg = "((?:[a-zA-Z])(?:[a-zA-Z0-9]|_)*)".r
  val LSAnyValReg = "_".r
  //    val SynthLSVar = "LS_(\\d*)".r
  def convert(arg:String):PureExpr=arg match {
    case LSVarReg(v) => NamedPureVar(v)
    case LSAnyValReg(_) => TopVal
    case LSNullConstReg() => NullVal
    case LSBoolConstReg(b) => BoolVal(b.toBoolean)
    case v => throw new IllegalArgumentException(s"Error parsing LSExpr $v")
  }
  def convertList(l:List[String]):List[PureExpr] = l.map(convert)
}

object LifeState {

    object LifeStateParser extends RegexParsers {
    //Note: this parser is only used for the "NonNullReturnCallins.txt"
    // specification are written in scala in the Specifications.scala source file
    sealed trait Ast
    case class AstID(s:String) extends Ast
    case class AstNI(v1:AstID, v2:AstID) extends Ast
    case class AstNot(v1:Ast) extends Ast
    case class AstOr(v1:Ast, v2:Ast) extends Ast
    case class AstAnd(v1:Ast, v2:Ast) extends Ast
    case object AstTrue extends Ast
    case object AstFalse extends Ast

    sealed trait Line
    case class AstMac(id:AstID, i:Once) extends Line
    case class AstRule(v1:Ast, tgt:AstID) extends Line
    // TODO: identifier should handle arrays, for now use java.util.List_ instead of java.util.List[]

    def pkIdentifier: Parser[String] = """([_a-zA-Z][.a-zA-Z0-9_]*)""".r ^^ {
      case v if v == "_" => ".*"
      case v if v.startsWith("_") => throw new IllegalArgumentException("Cannot start pkg identifier with underscore")
      case v => v
    }

    def pureExpr: Parser[PureExpr] = """([_a-zA-Z][.a-zA-Z0-9_]*)""".r ^^ {
      case v if v=="_" => TopVal
      case v: String => NamedPureVar(v)
    }

    def macroIdentifier:Parser[AstID] = """#[a-zA-Z][.a-zA-Z0-9_]*""".r ^^ {
      case ident => AstID(ident.drop(1))
    }

    def astMac:Parser[AstMac] = macroIdentifier ~ "=" ~ i ^^{
      case id ~ _ ~ lhs => AstMac(id, lhs)
    }

    //parse everything except I
    def lsRule :Parser[AstRule] = ???

    // parse I
    def empty: Parser[TopVal.type] = "_" ^^ {_ => TopVal}

//    def parMatcher:Parser[String] = pkIdentifier  //TODO: and const

    def mDir: Parser[MessageType] = ( "ciret" | "cbret" | "ci" | "cb") ^^ {
      case "ci" => CIEnter
      case "cb" => CBEnter
      case "ciret" => CIExit
      case "cbret" => CBExit
    }
    def sep = "&&"
    def op: Parser[CmpOp] = ("<:"|"="|"!=")^^ {
      case "=" => Equals
      case "!=" => NotEquals
      case "<:" => TypeComp
    }
    def constr:Parser[LSConstraint] = pureExpr ~ op ~ pureExpr^^ {
      case id1 ~ op ~ id2 =>
        LSConstraint(id1.asInstanceOf[PureVar], op, id2)

    }
    def constrs:Parser[List[LSConstraint]] = repsep(constr,sep)

    def lsVarList:Parser[List[PureExpr]] = repsep(pureExpr,",")

    def params = repsep(pkIdentifier, ",")

//    def rf(v:PureExpr):String = v.toString.replace("_","[^,()]*")
    //    def rf(v:String):String = v.replace("_","[^,()]*")


    def i: Parser[Once] = "I(" ~ mDir ~ "[" ~ lsVarList ~"]" ~ pkIdentifier ~ pkIdentifier ~"(" ~ params ~ ")" ~ constr ~ ")" ^^ {
      case _ ~ pmDir ~ _ ~ vars ~ _ ~ ret ~ sName ~ _ ~ para ~ _ ~ LSConstraint(v1, TypeComp, v2) ~ _ =>
        assert(vars.size < 2 || vars(1) == TopVal || vars(1) == v1, "Can only specify receiver type in I")
//        val p = para.map(rf)
        val sigRegex = ret + " " + sName + "\\(" +  para.mkString(",") + "\\)"
        val ident = ret + "__" + sName + "__" + para.mkString("___")
        val subtypeOf:String = v2.asInstanceOf[NamedPureVar].n //TODO: stupid hack, should be Class val somehow
        val scm = SubClassMatcher(subtypeOf, sigRegex, ident)
        Once(pmDir, scm, vars)
      case _ =>
        throw new IllegalArgumentException("Can only specify receiver type in I")
    }
    val lsTrueConst = "@(TRUE|true|True)".r ^^ {case _ => LSTrue}
    val lsFalseConst = "@(false|False|FALSE)".r ^^ {case _ => LSFalse}
    //    val lsNullConst = "@(?:null|Null|NULL)".r ^^ {case _ => LSNullConst}
    val lsConst = lsTrueConst | lsFalseConst
    val andTerm = "&&"
    val notTerm = "!"

//    def ni : Parser[NI] = "NI(" ~ i ~ "," ~ i ~ ")" ^^{
//      case _ ~ i1 ~ _ ~ i2 ~ _ => NI(i1,i2)
//    }
//    def lsAtom : Parser[LSAtom] = ni | i
//
//
//    def lsAnd : Parser[LSPred] = lsPred ~ andTerm ~ lsPred ^^{ case lhs ~ _ ~ rhs => And(lhs,rhs)}
//    def lsOr : Parser [LSPred] = lsPred ~ "||" ~ lsPred ^^ {case lhs ~ _ ~ rhs => Or(lhs,rhs)}
//    def lsNot =
//      ( notTerm ~> (lsAtom | macroIdentifier) ) ^^ { case p => Not(p)}
//    def lsGroup : Parser[LSPred] =
//      "{" ~> lsPred <~ "}" ^^ {case p  => p}
//    def lsPred : Parser[LSPred] =  lsAnd | lsOr | macroIdentifier | lsNot | lsAtom | lsConst
//
//    //    def lsRuleLHS:Parser[LSAtom] = i | macroIdentifier
//    def lsRuleUnc : Parser[LSSpec] = ( lsPred ~ "<=" ~ i) ^^ {
//      case pred ~ _ ~ (tgt:I) => LSSpec(pred, tgt)
//    }
//
//    def lsRule : Parser[LSSpec] = lsRuleUnc //| lsRuleCon
//    def lsLine :Parser[LSMacroAndSpec] = lsRuleUnc
  }
  def parseI(str:String):Once = {
    val res: LifeStateParser.ParseResult[Once] = LifeStateParser.parseAll(LifeStateParser.i, str)
    if(res.successful)
      res.get
    else
      throw new IllegalArgumentException(res.toString)
  }
  def parseIFile(str:String):Seq[Once] = {
    str.split("\n").filter(v => !v.trim.startsWith("#") && !(v.trim == "")).map(parseI)
  }

//  def parseSpec(str:String):Set[LSSpec] = {
//    val withoutComments = str.split("\n").filter{v => !v.trim.startsWith("#") && !v.trim.isEmpty }.mkString("\n")
//    if(withoutComments == ""){
//      return Set() // This is dumb, I shouldn't need to do this
//    }
//    val lines = withoutComments.split(";").map(_.trim).filter(_ != "")
//    val res = lines.map(line => {
//      val lineRes = LifeStateParser.parseAll(???, line)
//      if (lineRes.successful) {
//        lineRes.get
//      } else throw new IllegalStateException(lineRes.toString)
//    })
//    res.toSet
//  }

//  var id = 0
//  def nextLsVar():String = {
//    val lsVar = "v" + id
//    id = id+1
//    lsVar
//  }

  // Const value matchers
//  object LSConstParser{
//    def unapply(arg: String): Option[PureVal] = arg match{
//      case LSBoolConst(sv) => Some(BoolVal(sv.toBoolean))
//      case LSNullConst() => Some(NullVal)
//      case _ => None
//    }
//  }



  case class LSConstraint(v1:PureVar,op:CmpOp,v2:PureExpr ) extends LSBexp {
    override def apply(assign: Assign, currentArgs:List[TVal]): Option[Assign] = {
      ???
    }
    override def swap(swapMap: Map[PureVar, PureVar]) = {
      def swapIfVar[T<:PureExpr](v: T):T= v match{
        case v2:PureVar if swapMap.contains(v2) => swapMap(v2).asInstanceOf[T]
        case v2 => v2
      }
      LSConstraint(swapIfVar(v1),op, swapIfVar(v2))
    }
    override def contains(mt: MessageType, sig: (String, String))(implicit ch: ClassHierarchyConstraints): Boolean =
      false

    override def lsVar: Set[PureVar] = Set(v1,v2).flatMap {
      case sVar: PureVar => Some(sVar)
      case _ => None
    }

    override def toString(): String = op match {
      case Equals => s"[ $v1 == $v2 ]"
      case NotEquals => s"[ $v1 != $v2 ]"
      case TypeComp => s"[ $v1 : $v2 ]"
    }

    override def toTex: String = op match {
      case Equals => s"${arg2tex(v1)} = ${arg2tex(v2)}"
      case NotEquals =>s"${arg2tex(v1)} \\neq ${arg2tex(v2)}"
    }
  }
  object LSConstraint{
    def mk(v1:PureExpr, op:CmpOp, v2:PureExpr):LSPred = (v1,op,v2) match {
      case (v1:PureVal, Equals, v2:PureVal) if v1 == v2 => LSTrue
      case (v1:PureVal, Equals, v2:PureVal) if v1 != v2 => LSFalse
      case (v1:PureVal, NotEquals, v2:PureVal) if v1 != v2 => LSTrue
      case (v1:PureVal, NotEquals, v2:PureVal) if v1 == v2 => LSFalse
      case (v1:PureVar, op, v2:PureExpr) => LSConstraint(v1,op,v2)
      case (v1:PureExpr, Equals, v2:PureVar) => LSConstraint(v2,op,v1)
      case (v1:PureExpr, NotEquals, v2:PureVar) => LSConstraint(v2,op,v1)
    }
    implicit val rw:RW[LSConstraint] = macroRW
  }

  sealed trait LSPred {
    def toTex:String

    def swap(swapMap: Map[PureVar, PureVar]):LSPred

    def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints):Boolean

    def lsVar: Set[PureVar]
  }
  object LSPred{
    implicit var rw:RW[LSPred] = RW.merge(LSConstraint.rw, LSAtom.rw, macroRW[Forall], macroRW[Exists], macroRW[Not], macroRW[And],
      macroRW[Or], macroRW[LSTrue.type], macroRW[LSFalse.type], macroRW[UComb])
  }

  sealed trait LSBexp extends LSPred{
    /**
     * process transfer in register machine
     * @param assign from variables to concrete values
     * @param currentArgs arguments from the current message
     * @return
     */
    def apply(assign:Assign, currentArgs:List[TVal]):Option[Assign]
  }

  case class Forall(vars:List[PureVar], p:LSPred) extends LSPred{
//    override def toString:String =
//      if(vars.isEmpty) p.toString else s"Forall([${vars.mkString(",")}], ${p.toString})"
    override def toTex: String = ???
    override def swap(swapMap: Map[PureVar, PureVar]): Forall = {
      assert(!vars.exists(v => swapMap.contains(v)),
        s"Swap failed, quantified forall vars $vars overlaps with swapMap: $swapMap ")
      Forall(vars, p.swap(swapMap))
    }

    override def contains(mt: MessageType, sig: (String, String))(implicit ch: ClassHierarchyConstraints): Boolean = ???

    override def lsVar: Set[PureVar] = p.lsVar.removedAll(vars)

    override def toString(): String =
      if(vars.nonEmpty)
        s"Ɐ ${vars.mkString(",")} . $p"
      else
        p.toString
  }

  case class Exists(vars:List[PureVar], p:LSPred) extends LSPred {
    //    override def toString:String =
    //      if(vars.isEmpty) p.toString else s"Exists([${vars.mkString(",")}],${p.toString})"
    override def swap(swapMap: Map[PureVar, PureVar]): Exists = {
      assert(!vars.exists(v => swapMap.contains(v)),
        s"Swap failed, quantified exist vars $vars overlaps with swapMap: $swapMap ")
      Exists(vars, p.swap(swapMap))
    }

    override def contains(mt: MessageType, sig: (String, String))(implicit ch: ClassHierarchyConstraints): Boolean = ???

    override def lsVar: Set[PureVar] = p.lsVar.removedAll(vars)
    override def toString: String =
      if(vars.nonEmpty)
        s"∃ ${vars.mkString(",")} . $p"
      else
        p.toString

    override def toTex: String = ???
  }

  case class CLInit(sig:String) extends LSSingle {
    override def lsVars: List[PureVar] = Nil

    override def identitySignature: String =
      throw new IllegalStateException("No valid identity signature for CLInit")

    override def swap(swapMap: Map[PureVar, PureVar]): CLInit = this

    override def contains(mt: MessageType, sig: (String, String))(implicit ch: ClassHierarchyConstraints): Boolean =
      false

    override def lsVar: Set[PureVar] = Set()

    override def toTex: String = ???
  }
  object CLInit{
    implicit var rw:RW[CLInit] = macroRW
  }

  /**
   * V cannot appear in the trace before ref
   * ref occurs when the value must have been created or first seen at that point (e.g. new or cb v.<init>())
   * @param v
   */
  case class FreshRef(v: PureVar) extends LSSingle {
    override def contains(mt: MessageType, sig: (String, String))(implicit ch: ClassHierarchyConstraints): Boolean =
      false

    override def lsVar: Set[PureVar] = Set(v)

    override def identitySignature: String = s"FreshRef($v)"

    override def lsVars: List[PureVar] = lsVar.toList

    override def swap(swapMap: Map[PureVar, PureVar]): LifeState.FreshRef = {
      FreshRef(swapMap.getOrElse(v,v))
    }

    override def toString: String = v.toString

    override def toTex: String = ???
  }
  object FreshRef{
    private def oneCont(a1:LSPred, a2:LSPred):Option[FreshRef] = {
      val a1_ = containsRefV(a1)
      lazy val a2_ = containsRefV(a2)
      if(a1_.isEmpty) a2_ else a1_
    }
    def containsRefV(a: LSPred):Option[FreshRef] = a match{
      case v@FreshRef(_) => Some(v)
      case Not(a) => containsRefV(a)
      case And(a1,a2) => oneCont(a1,a2)
      case Or(a1,a2) => oneCont(a1,a2)
      case LSTrue => None
      case LSFalse => None
      case _:NS => None
      case _:Once => None
    }

    implicit var rw:RW[FreshRef] = macroRW
  }

  val LSGenerated = "LS_.*".r

  case class LSImplies(l1:LSPred, l2:LSPred) extends LSPred{
    override def swap(swapMap: Map[PureVar, PureVar]) = LSImplies(l1.swap(swapMap), l2.swap(swapMap))

    override def contains(mt: MessageType, sig: (String, String))(implicit ch: ClassHierarchyConstraints): Boolean =
      l1.contains(mt,sig) || l2.contains(mt,sig)

    override def lsVar: Set[PureVar] = l1.lsVar.union(l2.lsVar)

    override def toString: String = s"[ ${l1} ➡ ${l1} ]"

    override def toTex: String = ???
  }
  case class UComb(name:String, dep:List[LSPred], argNegated:Boolean=false) extends LSPred{
    override def toTex: String = ???

    override def swap(swapMap: Map[PureVar, PureVar]): LSPred = this.copy(dep = dep.map(p => p.swap(swapMap)))

    override def contains(mt: MessageType, sig: (String, String))(implicit ch: ClassHierarchyConstraints): Boolean = {
      dep.exists{p => p.contains(mt,sig)}
    }

    override def lsVar: Set[PureVar] = dep.flatMap{p => p.lsVar}.toSet
  }
  case class And(l1 : LSPred, l2 : LSPred) extends LSBexp {

    override def apply(assign: Assign, currentArgs:List[TVal]): Option[Assign] = {
      ???
    }
    override def lsVar: Set[PureVar] = l1.lsVar.union(l2.lsVar)

    override def contains(mt:MessageType, sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean =
      l1.contains(mt,sig) || l2.contains(mt,sig)

    override def swap(swapWithFresh: Map[PureVar, PureVar]) =
      And(l1.swap(swapWithFresh), l2.swap(swapWithFresh))

    override def toString: String = (l1,l2) match {
      case (LSFalse, _) => LSFalse.toString
      case (_, LSFalse) => LSFalse.toString
      case (LSTrue, l) => l.toString
      case (l, LSTrue) => l.toString
      case (l1,l2) => s"[ ${l1} && ${l2} ]"
    }

    override def toTex: String = s"${l1.toTex} \\wedge ${l2.toTex}"
  }
  case class Not(l: LSPred) extends LSAtom {
    override def lsVar: Set[PureVar] = l.lsVar

    override def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean =
      l.contains(mt,sig)

    override def swap(swapMap: Map[PureVar, PureVar]) = Not(l.swap(swapMap))

    override def toString: String = s"(Not ${l})"

    override def toTex: String = l match {
      case i: Once=> s"\\notiDir{${i.mToTex}}"
      case _ => ??? //s"\\neg ${l.toTex}"
    }

    override def identitySignature: String = l match {
      case once: Once => once.identitySignature
      case bexp: LSBexp => ???
      case Forall(vars, p) => ???
      case Exists(vars, p) => ???
      case LSImplies(l1, l2) => ???
      case UComb(name, dep, argNegated) => ???
      case atom: LSAtom => ???
    }
  }
  case class Or(l1:LSPred, l2:LSPred) extends LSBexp {

    override def apply(assign: Assign, currentArgs:List[TVal]): Option[Assign] = {
      ???
    }
    override def lsVar: Set[PureVar] = l1.lsVar.union(l2.lsVar)
    override def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean =
      l1.contains(mt, sig) || l2.contains(mt,sig)

    override def swap(swapMap: Map[PureVar, PureVar]) = Or(l1.swap(swapMap), l2.swap(swapMap))

    override def toString: String = (l1, l2) match {
      case (LSFalse, l) => l.toString
      case (l, LSFalse) => l.toString
      case (LSTrue, _) => LSTrue.toString
      case (_, LSTrue) => LSTrue.toString
      case (l1,l2) => s"[${l1} || ${l2}]"
    }

    override def toTex: String = s"${l1.toTex} \\vee ${l2.toTex}"
  }
  case object LSTrue extends LSBexp {
    override def apply(assign: Assign, currentArgs:List[TVal]): Option[Assign] = Some(assign)
    override def lsVar: Set[PureVar] = Set.empty
    override def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean = false

    override def swap(swapMap: Map[PureVar, PureVar]) = this

    override def toString: String = "True"

    override def toTex: String = "\\enkwTrue"
  }
  case object LSFalse extends LSBexp {
    override def apply(assign: Assign, currentArgs:List[TVal]): Option[Assign] = None
    override def lsVar: Set[PureVar] = Set.empty
    override def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean = false

    override def swap(swapMap: Map[PureVar, PureVar]) = this

    override def toString: String = "False"

    override def toTex: String = "\\enkwFalse"
  }

  sealed trait LSAtom extends LSPred {
//    def getAtomSig:String
    def identitySignature:String
  }
  object LSAtom{
    implicit val rw:RW[LSAtom] = RW.merge(NS.rw, LSSingle.rw)
  }

  sealed trait SignatureMatcher{
    def toTex(args:List[PureExpr]):String

    def matchesClass(sig: String):Boolean

    def matchesSubSig(subsig:String):Boolean
    def matches(sig:(String,String))(implicit ch:ClassHierarchyConstraints):Boolean
    def identifier:String
  }
  object SignatureMatcher{
    implicit val rw:RW[SignatureMatcher] = RW.merge(SetSignatureMatcher.rw, SubClassMatcher.rw)
  }
  @Deprecated
  case class SetSignatureMatcher(sigSet : Set[(String,String)]) extends SignatureMatcher {
    override def matches(sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean = sigSet.contains(sig)

    override def matchesSubSig(subsig: String): Boolean = sigSet.exists(v => subsig == v._2)

    private val sortedSig = sigSet.toList.sorted
    override def identifier: String =s"${sortedSig.head._1}_${sortedSig.head._2}"

    override def matchesClass(sig: String): Boolean = ???

    override def toTex(args:List[PureExpr]): String = ???
  }
  object SetSignatureMatcher{
    implicit val rw:RW[SetSignatureMatcher] = macroRW
  }

  /**
   *
   * @param baseSubtypeOf match any callin where the defining class is a subtype of this
   * @param signatureMatcher regular expression matching soot style signature
   * @param ident unique name for matcher used by trace solver
   */
  case class SubClassMatcher(baseSubtypeOf:Set[String], signatureMatcher:String, ident:String) extends SignatureMatcher {
    assert(!signatureMatcher.contains('(') || signatureMatcher.contains('\\'),
      "Signature matcher is regular exppression. Parentheses must be escaped. e.g. \\\\(\\\\)")
    lazy val sigR:Regex = signatureMatcher.r
    override def matches(sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean = {
      if(!matchesSubSig(sig._2)){
        return false
      }
      baseSubtypeOf.exists { bt =>
        if (ch.typeExists(bt)) { // Specs may not match any type if library has not been included in apk
          ch.getSubtypesOf(bt).contains(sig._1)
        } else false
      }
    }

    override def matchesSubSig(subsig: String): Boolean = {
      sigR.matches(subsig)
    }

    override def identifier: String = ident

    override def matchesClass(sig: String): Boolean = baseSubtypeOf.contains(sig)


    override def toTex(argsin:List[PureExpr]): String = {
      val args = argsin.map(v => arg2tex(v))
      ident match {
        case i if i.contains("onCreate") =>
          assert(args.head == "_")
          s"\\codej{${args(1)}.onCreate()}"
        case i if i.contains("onDestroy") =>
          s"\\codej{${args(1)}.onDestroy()}"
        case i if i.contains("onActivityCreated") =>
          s"\\codej{${args(1)}.onActivityCreated()}"
        case i if i.contains("onPause") =>
          assert(args.head == "_")
          s"\\codej{${args(1)}onPause()}"
        case i if i.contains("onResume") =>
          assert(args.head == "_")
          s"\\codej{${args(1)}.onResume()}"
        case i if i.contains("call") =>
          assert(args.head == "_")
          s"\\codej{${args(1)}.call()}"
        case i if i.contains("unsubscribe") =>
          assert(args.head == "_")
          s"\\codej{${args(1)}.unsubscribe()}"
        case i if i.contains("subscribe") =>
          s"\\codej{${args(0)}:= \\_.subscribe(${if(args.size > 2) args(2) else ""})}"
        case i if i.contains("setOnClickListener") =>
          s"\\codej{${args(1)}.setOnClickListener(${args(2)})}"
        case i if i.contains("show") =>
          s"\\codej{${args(0)} := \\_.show(${if(args.size > 2) args(2) else ""})}"
        case i if i.contains("onClick") =>
          s"\\codej{${args(1)}.onClick()}"
        case i if i.contains("findView") =>
          s"\\codej{${args(0)}:=${args(1)}.findViewById(\\_)}"
        case i if i.contains("finish") =>
          s"\\codej{${args(1)}.finish()}"
        case i if i.contains("getActivity") =>
          s"\\codej{${args(0)} := ${args(1)}.getActivity()}"
        case i if i.contains("dismiss") =>
          s"\\codej{${args(1)}.dismiss()}"
        case i if i.contains("setEnabled") =>
          s"\\codej{${args(1)}.setEnabled(${args(2)})}"
        case i if i.contains("execute") =>
          s"\\codej{${args(1)}.execute()}"
        case other =>
          println(other)
          ???
    }
    }
  }
  object SubClassMatcher{
    def apply(baseSubtypeOf:String, signatureMatcher: String, ident:String):SubClassMatcher =
      SubClassMatcher(Set(baseSubtypeOf), signatureMatcher, ident)
    implicit val rw:RW[SubClassMatcher] = macroRW
  }
  // A method with a signature in "signatures" has been invoed
  // lsVars: element 0 is return value, element 1 is reciever, rest of the elements are arguemnts
  // A string of "_" means "don't care"
  // primitives are parsed as in java "null", "true", "false", numbers etc.
  sealed trait LSSingle extends LSAtom {
    def lsVars: List[PureExpr]
  }
  object LSSingle{
    implicit val rw:RW[LSSingle] = RW.merge(Once.rw, FreshRef.rw, CLInit.rw)
  }

  case class Once(mt: MessageType, signatures: SignatureMatcher, lsVars : List[PureExpr]) extends LSSingle {
    //    def constVals(constraints: Set[LSConstraint]):List[Option[(CmpOp, PureExpr)]] = lsVars.map{
    //      case LifeState.LSConst(v) => Some((Equals, v))
    //      case LifeState.LSVar(v) =>
    //        constraints.find(c => c.v1 == v || c.v2 == v) match {
    //          case Some(LSConstraint(_, op, LifeState.LSConst(v2))) => Some(op,v2)
    //          case Some(LSConstraint(LifeState.LSConst(v1), op, _)) => Some(op,v1)
    //          case None => None
    //          case c => throw new IllegalStateException(s"Malformed constraint: $c")
    //        }
    //      case _ => None
    //    }
    override def lsVar: Set[PureVar] = lsVars.flatMap {
      case pureVar: PureVar => Some(pureVar)
      case _: PureVal => None
    }.toSet

    def getVar(i: Int): PureExpr = lsVars(i)


//    override def getAtomSig: String = {
//      s"I(${sortedSig.mkString(":")})"
//    }

    // Uesed for naming uninterpreted functions in z3 solver
    override def identitySignature: String = {
      // Note: this does not include varnames or
      // any other info that would distinguish this I from another with the same metods
      s"I_${mt.toString}_${signatures.identifier}"
    }

    override def contains(omt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean =
      omt == mt && signatures.matches(sig)

    override def swap(swapMap: Map[PureVar, PureVar]): Once = {
      val newLSVars = lsVars.map{
        case v:PureVar => swapMap.getOrElse(v,v)
        case c => c
      }
      this.copy(lsVars = newLSVars)
    }

    override def toString : String =
      s"O($mt $identitySignature ( ${lsVars.mkString(",")} )"

    def mToTex:String = s"${mt.toTex}~${signatures.toTex(lsVars)}"

    override def toTex: String = s"\\iDir{${mToTex}}"
  }
  object Once{
    implicit val rw:RW[Once] = macroRW
  }
  // Since i1 has been invoked, i2 has not been invoked.
  case class NS(i1:Once, i2:Once) extends LSAtom{
    //assert(i2.lsVar.forall(x => i1.lsVar.contains(x)), "Free variables of i2 must be subset of free variables of i1")
    lazy val lsVar: Set[PureVar] = i1.lsVar.union(i2.lsVar)

//    override def getAtomSig: String = s"NI(${i1.getAtomSig}, ${i2.getAtomSig})"

    override def identitySignature: String = s"${i1.identitySignature}_${i2.identitySignature}"

    override def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean =
      i1.contains(mt, sig) || i2.contains(mt, sig)

    override def swap(swapMap: Map[PureVar, PureVar]) = NS(i1.swap(swapMap), i2.swap(swapMap))

    override def toString: String = s"NS( $i1 , $i2 )"

    override def toTex: String = s"\\niDir{${i2.mToTex}}{${i1.mToTex}}"
  }
  object NS{
    implicit val rw:RW[NS] = macroRW
  }
  case class LSSpec(univQuant:List[PureVar], existQuant:List[PureVar],
                    pred:LSPred, target: Once, rhsConstraints: Set[LSConstraint] = Set()){
    def toTex():String = {
      // in paper language, universal quantification of target vars is implicit
      val dispUnivQuant = univQuant.toSet -- target.lsVar

      val faQuant = if(dispUnivQuant.nonEmpty) s"\\forall ${dispUnivQuant.mkString(",")}." else ""
      // existential quantification of matcher variables is implicit
      // val exQuant = if(existQuant.nonEmpty) s"\\exists ${existQuant.mkString(",")}." else ""
      val tgtStr = if(rhsConstraints.isEmpty)
        target.mToTex
      else if(rhsConstraints.exists{
        case LSConstraint(v, Equals, NullVal) => true
        case _ => false
      }) {
        target.copy(lsVars = target.lsVars.map{
          case v2 if v2 == rhsConstraints.head.v1 => NullVal
          case v => v
        }).mToTex
      } else
        ???
      val out = s"\\specOnly{\\ensuremath{$tgtStr}}{\\ensuremath{${faQuant}${pred.toTex}}}"
      out
    }

    private def checkWF(quant:Set[PureVar], p:LSPred):Boolean = p match {
      case LSConstraint(v1, _, v2:PureVar) => quant.contains(v1) && quant.contains(v2)
      case LSConstraint(v1, _, v2) => quant.contains(v1)
      case Forall(vars, p) => checkWF(quant ++ vars,p)
      case Exists(vars, p) => checkWF(quant ++ vars,p)
      case LSImplies(l1, l2) => checkWF(quant,l1) && checkWF(quant,l2)
      case And(l1, l2) => checkWF(quant,l1) && checkWF(quant,l2)
      case Not(l) => checkWF(quant,l)
      case Or(l1, l2) => checkWF(quant,l1) && checkWF(quant,l2)
      case LSTrue => true
      case LSFalse => true
      case i:LSAtom => i.lsVar.forall(v => quant.contains(v))
      case UComb(_,preds,_) => preds.forall(p => checkWF(quant,p))
      case v =>
        throw new IllegalArgumentException(s"${v} is not a valid lspred")
    }
    private def checkWellFormed():Unit = {
      val quantified = univQuant.toSet ++ existQuant
      if(!(checkWF(quantified, pred) && checkWF(quantified,target)))
        throw new IllegalArgumentException("mismatch between quantified variables and free variables")
    }
    checkWellFormed()
    def instantiate(i:Once, specSpace: SpecSpace):LSPred = {
      if(i.signatures != target.signatures || i.mt != target.mt)
        return LSTrue

      val swappedTo = i.lsVar
      val swappedFrom = target.lsVar
      assert(swappedTo.intersect(this.target.lsVar).isEmpty, "Vars must not be duplicated")
      assert(swappedTo.intersect(this.pred.lsVar).isEmpty, "Vars must not be duplicated")

      // (swap from, swap to)
      val allPairs = (target.lsVars zip i.lsVars)

      // comparing pure vals results in true or false
      // (pval1, pval2) yields pval1 == pval2
      // comparing const val in target to const value from transfer results in comparison
      // (const1, pv) yields const2 == pv
      val purePreds:List[LSPred] = allPairs.flatMap{
        case (p1:PureVal, p2:PureExpr) =>
          Some(LSConstraint.mk(p1,Equals,p2))
        case _ => None
      }

      val toSwap: Map[PureVar,PureVar] = allPairs.flatMap{
        case (p1:PureVar, p2:PureVar) => Some(p1,p2)
        case (TopVal, _) => None
        case (_, TopVal) =>
          ???
        case (p1:PureVar, p2:PureExpr) =>
          ??? //TODO: refactor swap to accept PureExpr? (p1 won't exist after inst)
        case _ => None
      }.toMap

      assert(toSwap.keySet == swappedFrom,
        s"Must instantiate all vars. found: ${toSwap.keySet}, expected: ${swappedFrom}")

      val swapPred = Exists(existQuant, pred.swap(toSwap))
      assert(swapPred.lsVar.subsetOf(swappedTo),
        s"Free variables of instantiated spec must be subset of instantiating message. " +
          s"\nfound fv: ${swapPred.lsVar}" +
          s"\nrequired fv: ${swappedTo}" +
          s"\npossible malformed spec: ${this.toString}")

      val res: LSPred = (swapPred::purePreds).reduce(And)
      if(rhsConstraints.isEmpty)
        res
      else {
        val allC:Set[LSPred] = rhsConstraints.map(c => c.swap(toSwap).asInstanceOf[LSPred])
        LSImplies(allC.reduce(And), res)
      }
    }
  }
  object LSSpec{
    implicit val rw:RW[LSSpec] = macroRW
  }

  def arg2tex(v: PureExpr): String = v match {
    case pureVal: PureVal => ???
    case pureVar: PureVar => ???
    //    case LSVar(v) => v
    //    case LSNullConst() => "\\enkwNull"
    //    case LSBoolConst(v) if v.contains("rue") => "\\enkwTrue"
    //    case LSBoolConst(v) if v.contains("alse") => "\\enkwFalse"
    //    case LSAnyVal() => "_"
    //    case _ =>
    //      ???
  }

  // Class that holds a graph of possible predicates and alias relations between the predicates.
  // Generated from a fast pre analysis of the applications.
  // Set of vars that can alias are represented by having the same name.
  class PredicateSpace(predicates: Set[LSAtom]){
    /** mapping from variable names to predicates containing variable */
//    val findVars: Map[String, Set[LSAtom]] = predicates.foldLeft(Map[String, Set[LSAtom]]()) { (acc, v) =>
//      v.lsVar.foldLeft(acc){ (iacc, varname) => iacc + (varname -> (iacc.getOrElse(varname, Set()) + v) )}
//    }

    /**
     *
     * @param src source of alias edge (index, atom sig)
     * @param tgt target of alias edge (index, atom sig)
     */
    case class Edge(src: (Int, String), tgt: (Int, String))

//    def getEdgeSet: Set[Edge] = {
//      val varmap: Map[String, Set[(Int, String)]] =
//        predicates.foldLeft(Map[String, Set[(Int,String)]]()) { (acc, predicate) => {
//          predicate.lsVar.zipWithIndex.foldLeft(acc){(iacc, v) => {
//            val oldSet: Set[(Int, String)] = iacc.getOrElse(v._1, Set())
//            val newPar: (Int, String) = (v._2, predicate.getAtomSig)
//            iacc + (v._1 -> (oldSet + newPar))
//          }
//         }
//        }}
//      varmap.flatMap(a => {
//        val l = BounderUtil.repeatingPerm(_=> a._2, 2)
//        l.map(b => Edge(b.head, b(1))).toSet
//      }).toSet
//    }
  }
}
object SpecSpace{
  def allI(pred:Option[LSPred]):Set[Once] = pred match {
    case Some(v) => allI(v)
    case None => Set()
  }
  def allI(pred:LSPred):Set[Once] = pred match{
    case LSImplies(l1, l2) => allI(l1).union(allI(l2))
    case CLInit(_) => Set()
    case i@Once(_,_,_) => Set(i)
    case NS(i1,i2) => Set(i1,i2)
    case And(p1,p2) => allI(p1).union(allI(p2))
    case Or(p1,p2) => allI(p1).union(allI(p2))
    case Not(p) => allI(p)
    case LSTrue => Set()
    case LSFalse => Set()
    case FreshRef(_) => Set()
    case Forall(_,p) => allI(p)
    case Exists(_,p) => allI(p)
    case LSConstraint(_,_, _) => Set()
    case UComb(_, dep,_)=> dep.flatMap(d => allI(d)).toSet
  }
  def allI(spec:LSSpec, includeRhs:Boolean = true):Set[Once] = spec match{
    case LSSpec(_,_,pred, target,_) if includeRhs => allI(pred).union(allI(target))
    case LSSpec(_,_,pred, target,_) => allI(pred)
  }
}
/**
 * Representation of a set of possible lifestate specs */
class SpecSpace(enableSpecs: Set[LSSpec], disallowSpecs:Set[LSSpec] = Set()) {
  def findIFromCurrent(dir: MessageType, signature: (String, String))(implicit cha:ClassHierarchyConstraints):Set[Once] = {
    allI.filter(i => i.mt == dir && i.signatures.matches(signature))
  }

  def specsByI(i: Once) = {
    val ids = i.identitySignature
    val specs = enableSpecs.filter(spec => spec.target.identitySignature == ids)
    specs
  }
  def disSpecsByI(i:Once) = {
    val ids = i.identitySignature
    val disSpecs = disallowSpecs.filter(spec => spec.target.identitySignature == ids)
    disSpecs
  }

  private var allIMemo:Option[Set[Once]] = None
  def allI:Set[Once] ={
    if(allIMemo.isEmpty)
      allIMemo = Some((enableSpecs ++ disallowSpecs).flatMap{spec =>
        SpecSpace.allI(spec.pred) + spec.target
      })
    allIMemo.get
  }

  def getSpecs:Set[LSSpec] = enableSpecs
  private val allISpecs: Map[MessageType, Set[Once]] =
    (enableSpecs ++ disallowSpecs).flatMap(SpecSpace.allI(_)).groupBy(i => i.mt)


//  private var freshLSVarIndex = 0
//  def nextFreshLSVar():String = {
//    val ind = freshLSVarIndex
//    freshLSVarIndex = freshLSVarIndex+1
//    s"LS__${ind}"
//  }
  /**
   * For step back over a place where the code may emit a message find the applicable I and assign fresh ls vars.
   * Return has arbitrary non-top pure expr for arguments that matter, top for ones that don't.
   * Caller must replace all non-top pure expr with something from abstract state.
   * @param mt Direction of message
   * @param sig class name and method signature (e.g. void foo(java.lang.Object))
   * @return Some(I) if I exists, None otherwise.
   */
  def getIWithMergedVars(mt: MessageType, sig: (String, String))
                        (implicit ch : ClassHierarchyConstraints):Option[Once] = {
    //    iset.get(mt,sig).map{i =>
    //      i.copy(lsVars = i.lsVars.map(a => if(a != "_") nextFreshLSVar() else "_"))
    //    }
    def merge(v:(PureExpr,PureExpr)):PureExpr = v match{
      case (TopVal,v) => v
      case (v,_) => v
    }
    var solverSig:Option[String] = None
    val out: Set[Once] = allI.filter{ i =>
      if(i.signatures.matches(sig) && i.mt == mt) {
        if (solverSig.isDefined) {
          assert(i.identitySignature == solverSig.get,
            s"Multiple I identity signatures match method: ${sig} I1: ${i.identitySignature} I2: ${solverSig.get}")
        } else {
          solverSig = Some(i.identitySignature)
        }
        true
      } else
        false
    }
    if(out.isEmpty)
      return None

    // Compute intersection of defined variables
    val parList = out.foldLeft(List():List[PureExpr]){
      case (acc,Once(_,_,vars)) =>
        acc.zipAll(vars,TopVal,TopVal).map(merge)
    }
//    val parListFresh = ??? //parList.map(a => if(a!="_") LSVarGen.getNext else "_")

    val headSig = out.headOption.map(i => i.identitySignature)
    assert(out.tail.forall(i => headSig.forall(v => v == i.identitySignature)),
      "All matched i must have same identity signature")
//    assert(out.size == 1 || out.isEmpty, "I must be unique for each message")
    //copy I with intersection of defined vars
    out.headOption.map(v => v.copy(lsVars = parList))
  }
//  def getRefWithFreshVars(): FreshRef ={
//    FreshRef(LSVarGen.getNext)
//  }

  /**
   * Find a lifestate spec by
   *
   * @param pkg
   * @param name
   * @return
   */
  def specsBySig(mt: MessageType, pkg:String, name:String)(implicit ch: ClassHierarchyConstraints):Set[LSSpec] = {
    // TODO: cache specs in hash map
    //    val getI = getIWithFreshVars(mt, (pkg,name)).map(_.identitySignature)
    val sig = (pkg,name)
    var solverSig:Option[String] = None
    val out: Set[Once] = allI.filter{ i =>
      if(i.signatures.matches(sig) && i.mt == mt) {
        if (solverSig.isDefined) {
          assert(i.identitySignature == solverSig.get,
            s"Multiple I identity signatures match method: ${sig} I1: ${i.identitySignature} I2: ${solverSig.get}")
        } else {
          solverSig = Some(i.identitySignature)
        }
        true
      } else
        false
    }
    val getI = out.map(_.identitySignature)
    val specsForSig = enableSpecs.filter(a => a.target.mt == mt && a.target.signatures.matches((pkg,name)))
    val identSigs: Set[String] = specsForSig.map(_.target.identitySignature) ++ getI
    identSigs.reduceOption((a:String,b:String) => {
      assert(a == b, s"Mismatched identity signatures: ${a} and ${b}")
      a
    })
    specsForSig
  }

}

class SpecAssignment(){

}

