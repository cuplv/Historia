package edu.colorado.plv.bounder.lifestate

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{CBEnter, CBExit, CIEnter, CIExit, MessageType, RVal}
import edu.colorado.plv.bounder.lifestate.LSPredAnyOrder.{countAny, predDepth, rankPred, rankSpecSpace}
import edu.colorado.plv.bounder.lifestate.LifeState.{AbsMsg, And, AnyAbsMsg, CLInit, Exists, Forall, FreshRef, HNOE, LSAnyPred, LSConstraint, LSFalse, LSImplies, LSPred, LSSpec, LSTrue, NS, Not, OAbsMsg, Or, Signature, SubClassMatcher}
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, EncodingTools}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BoolVal, BotVal, CmpOp, Equals, IntVal, NPureVar, NamedPureVar, NotEquals, NullVal, PureExpr, PureVal, PureVar, RelevantNotDefined, State, TopVal, TypeComp}

import scala.util.parsing.combinator._
import upickle.default.{macroRW, ReadWriter => RW}

import java.util.Objects
import scala.collection.mutable
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
    case class AstMac(id:AstID, i:AbsMsg) extends Line
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


    def i: Parser[AbsMsg] = "I(" ~ mDir ~ "[" ~ lsVarList ~"]" ~ pkIdentifier ~ pkIdentifier ~"(" ~ params ~ ")" ~ constr ~ ")" ^^ {
      case _ ~ pmDir ~ _ ~ vars ~ _ ~ ret ~ sName ~ _ ~ para ~ _ ~ LSConstraint(v1, TypeComp, v2) ~ _ =>
        assert(vars.size < 2 || vars(1) == TopVal || vars(1) == v1, "Can only specify receiver type in I")
//        val p = para.map(rf)
        val sigRegex = ret + " " + sName + "\\(" +  para.mkString(",") + "\\)"
        val ident = ret + "__" + sName + "__" + para.mkString("___")
        val subtypeOf:String = v2.asInstanceOf[NamedPureVar].n //TODO: stupid hack, should be Class val somehow
        val scm = SubClassMatcher(subtypeOf, sigRegex, ident)
        OAbsMsg(pmDir, scm, vars)
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
  def parseI(str:String):AbsMsg = {
    val res: LifeStateParser.ParseResult[AbsMsg] = LifeStateParser.parseAll(LifeStateParser.i, str)
    if(res.successful)
      res.get
    else
      throw new IllegalArgumentException(res.toString)
  }
  def parseIFile(str:String):Seq[AbsMsg] = {
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
    override def swap(swapMap: Map[PureVar, PureExpr]) = {
      def swapIfVar(v: PureExpr):PureExpr= v match{
        case v2:PureVar if swapMap.contains(v2) => swapMap(v2)
        case v2 => v2
      }
      val v1Swap = swapIfVar(v1)
      val v2Swap = swapIfVar(v2)
      LSConstraint.mk(v1Swap,op,v2Swap)
    }
    override def contains(mt: MessageType, sig: Signature)(implicit ch: ClassHierarchyConstraints): Boolean =
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
      case TypeComp => s"${arg2tex(v1)} : ${arg2tex(v2)}"
    }

    override def lsVal: Set[PureVal] = v2 match {
      case pureVal: PureVal => Set(pureVal)
      case _ => Set.empty
    }

    override def allMsg: Set[OAbsMsg] = Set.empty
  }
  object LSConstraint{
    def mk(v1:PureExpr, op:CmpOp, v2:PureExpr):LSPred =
      (v1,op,v2) match {
        case (TopVal, _,_) => LSTrue
        case (_,_,TopVal) => LSTrue
        case (BotVal, _, _) => LSFalse
        case (_, _, BotVal) => LSFalse
        case (IntVal(1), op, BoolVal(true)) =>
          if(op == Equals) LSTrue else LSFalse
        case (IntVal(0), op, BoolVal(false)) =>
          if(op == Equals) LSTrue else LSFalse
        case (b:BoolVal, op, i:IntVal) => mk(i,op,b)
        case (v1: PureVal, Equals, v2: PureVal) if v1 == v2 => LSTrue
        case (v1: PureVal, Equals, v2: PureVal) if v1 != v2 => LSFalse
        case (v1:PureVal, NotEquals, v2:PureVal) if v1 != v2 => LSTrue
        case (v1:PureVal, NotEquals, v2:PureVal) if v1 == v2 => LSFalse
        case (v1:PureVar, op, v2:PureExpr) => LSConstraint(v1,op,v2)
        case (v1:PureExpr, Equals, v2:PureVar) => LSConstraint(v2,op,v1)
        case (v1:PureExpr, NotEquals, v2:PureVar) => LSConstraint(v2,op,v1)
        case v => throw new IllegalArgumentException(s"cannot make comp constraint: $v")
      }
    implicit val rw:RW[LSConstraint] = macroRW
  }

  sealed trait LSPred {
    def toTex:String

    def swap(swapMap: Map[PureVar, PureExpr]):LSPred
    def allMsg:Set[OAbsMsg]

    def contains(mt:MessageType,sig: Signature)(implicit ch:ClassHierarchyConstraints):Boolean

    def lsVar: Set[PureVar]

    def lsVal: Set[PureVal]
  }
  object LSPred{
    implicit var rw:RW[LSPred] = RW.merge(LSConstraint.rw, LSAtom.rw, macroRW[Forall], macroRW[Exists], macroRW[Not], macroRW[And],
      macroRW[Or], macroRW[LSTrue.type], macroRW[LSFalse.type])
  }

  case object LSAnyPred extends LSPred {
    override def toTex: String = "LSAny"

    override def swap(swapMap: Map[PureVar, PureExpr]): LSPred = LSAnyPred

    override def contains(mt: MessageType, sig: Signature)(implicit ch: ClassHierarchyConstraints): Boolean =
      throw new IllegalStateException("Contains called on LSAny")

    override def lsVar: Set[PureVar] = Set.empty

    override def lsVal: Set[PureVal] = Set.empty

    override def allMsg: Set[OAbsMsg] = Set.empty
  }
  sealed trait LSBexp extends LSPred{

  }

  sealed trait LSBinOp extends LSPred{
    def l1:LSPred
    def l2:LSPred
  }

  sealed trait LSUnOp extends LSPred{
    def p:LSPred
  }

  case class Forall(vars:List[PureVar], p:LSPred) extends LSPred with LSUnOp{
//    override def toString:String =
//      if(vars.isEmpty) p.toString else s"Forall([${vars.mkString(",")}], ${p.toString})"
    override def toTex: String = ???
    override def swap(swapMap: Map[PureVar, PureExpr]): Forall = {
      assert(!vars.exists(v => swapMap.contains(v)),
        s"Swap failed, quantified forall vars $vars overlaps with swapMap: $swapMap ")
      Forall(vars, p.swap(swapMap))
    }

    override def contains(mt: MessageType, sig: Signature)(implicit ch: ClassHierarchyConstraints): Boolean = ???

    override def lsVar: Set[PureVar] = p.lsVar.removedAll(vars)

    override def toString(): String =
      if(vars.nonEmpty)
        s"Ɐ ${vars.mkString(",")} . $p"
      else
        p.toString

    override def lsVal: Set[PureVal] = p.lsVal

    override def allMsg: Set[OAbsMsg] = p.allMsg
  }

  case class Exists(vars:List[PureVar], p:LSPred) extends LSPred  with LSUnOp {
    //    override def toString:String =
    //      if(vars.isEmpty) p.toString else s"Exists([${vars.mkString(",")}],${p.toString})"
    override def swap(swapMap: Map[PureVar, PureExpr]): Exists = {
      assert(!vars.exists(v => swapMap.contains(v)),
        s"Swap failed, quantified exist vars $vars overlaps with swapMap: $swapMap ")
      Exists(vars, p.swap(swapMap))
    }

    override def contains(mt: MessageType, sig: Signature)(implicit ch: ClassHierarchyConstraints): Boolean = ???

    override def lsVar: Set[PureVar] = p.lsVar.removedAll(vars)
    override def toString: String =
      if(vars.nonEmpty)
        s"∃ ${vars.mkString(",")} . $p"
      else
        p.toString

    override def toTex: String = ???

    override def lsVal: Set[PureVal] = p.lsVal

    override def allMsg: Set[OAbsMsg] = p.allMsg
  }

  case class CLInit(sig:String) extends LSSingle {
    override def lsVars: List[PureVar] = Nil

    override def identitySignature: String =
      throw new IllegalStateException("No valid identity signature for CLInit")

    override def swap(swapMap: Map[PureVar, PureExpr]): CLInit = this

    override def contains(mt: MessageType, sig: Signature)(implicit ch: ClassHierarchyConstraints): Boolean =
      false

    override def lsVar: Set[PureVar] = Set()

    override def toTex: String = ???

    override def lsVal: Set[PureVal] = Set.empty

    override def allMsg: Set[OAbsMsg] = Set.empty
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
    override def contains(mt: MessageType, sig: Signature)(implicit ch: ClassHierarchyConstraints): Boolean =
      false

    override def lsVar: Set[PureVar] = Set(v)

    override def identitySignature: String = s"FreshRef($v)"

    override def lsVars: List[PureVar] = lsVar.toList

    override def swap(swapMap: Map[PureVar, PureExpr]): LSPred = {
      swapMap.getOrElse(v,v) match{
        case v:PureVar => FreshRef(v)
        case NullVal => LSFalse
        case _ =>
          ??? //TODO: this probably happens with boxed values, figure out what to do later
      }
    }

    override def toString: String = v.toString

    override def toTex: String = ???

    override def lsVal: Set[PureVal] = Set.empty

    override def allMsg: Set[OAbsMsg] = ???
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
      case _:AbsMsg => None
      case Exists(_, p) => containsRefV(p)
      case Forall(_, p) => containsRefV(p)
      case CLInit(_) => None
      case LSAnyPred => None
      case LSConstraint(_, _, _) => None
      case LSImplies(l1, l2) => oneCont(l1,l2)
    }

    implicit var rw:RW[FreshRef] = macroRW
  }

  val LSGenerated = "LS_.*".r

  case class LSImplies(l1:LSPred, l2:LSPred) extends LSPred{
    override def swap(swapMap: Map[PureVar, PureExpr]) = LSImplies(l1.swap(swapMap), l2.swap(swapMap))

    override def contains(mt: MessageType, sig: Signature)(implicit ch: ClassHierarchyConstraints): Boolean =
      l1.contains(mt,sig) || l2.contains(mt,sig)

    override def lsVar: Set[PureVar] = l1.lsVar.union(l2.lsVar)

    override def toString: String = s"[ ${l1} ➡ ${l1} ]"

    override def toTex: String = ???

    override def lsVal: Set[PureVal] = l1.lsVal ++ l2.lsVal

    override def allMsg: Set[OAbsMsg] = l1.allMsg ++ l2.allMsg
  }

  case class And(l1 : LSPred, l2 : LSPred) extends LSBexp with LSBinOp {

    override def lsVar: Set[PureVar] = l1.lsVar.union(l2.lsVar)

    override def contains(mt:MessageType, sig: Signature)(implicit ch:ClassHierarchyConstraints): Boolean =
      l1.contains(mt,sig) || l2.contains(mt,sig)

    override def swap(swapWithFresh: Map[PureVar, PureExpr]) =
      And(l1.swap(swapWithFresh), l2.swap(swapWithFresh))

    override def toString: String = (l1,l2) match {
      case (LSFalse, _) => LSFalse.toString
      case (_, LSFalse) => LSFalse.toString
      case (LSTrue, l) => l.toString
      case (l, LSTrue) => l.toString
      case (l1,l2) => s"[ ${l1} && ${l2} ]"
    }

    override def toTex: String = s"${l1.toTex} \\wedge ${l2.toTex}"

    override def lsVal: Set[PureVal] = l1.lsVal ++ l2.lsVal

    override def allMsg: Set[OAbsMsg] = l1.allMsg ++ l2.allMsg
  }
  case class Not(p: LSPred) extends LSAtom with LSUnOp {
    //assert(p.isInstanceOf[OAbsMsg], "not only applicable to once")
    override def lsVar: Set[PureVar] = p.lsVar

    override def contains(mt:MessageType,sig: Signature)(implicit ch:ClassHierarchyConstraints): Boolean =
      p.contains(mt,sig)

    override def swap(swapMap: Map[PureVar, PureExpr]) = Not(p.swap(swapMap))

    override def toString: String = s"(Not ${p})"

    override def toTex: String = p match {
      case i: AbsMsg=> s"\\notiDir{${i.mToTex}}"
      case _ => ??? //s"\\neg ${l.toTex}"
    }

    override def identitySignature: String = p match {
      case once: AbsMsg => once.identitySignature
      case exp =>
        throw new IllegalArgumentException(s"identity sig only valid for AbsMsg and Not(AbsMsg), found: ${exp}")
    }

    override def lsVal: Set[PureVal] = p.lsVal

    override def allMsg: Set[OAbsMsg] = p.allMsg
  }
  case class Or(l1:LSPred, l2:LSPred) extends LSBexp with LSBinOp {

    override def lsVar: Set[PureVar] = l1.lsVar.union(l2.lsVar)
    override def contains(mt:MessageType,sig: Signature)(implicit ch:ClassHierarchyConstraints): Boolean =
      l1.contains(mt, sig) || l2.contains(mt,sig)

    override def swap(swapMap: Map[PureVar, PureExpr]) = Or(l1.swap(swapMap), l2.swap(swapMap))

    override def toString: String = (l1, l2) match {
      case (LSFalse, l) => l.toString
      case (l, LSFalse) => l.toString
      case (LSTrue, _) => LSTrue.toString
      case (_, LSTrue) => LSTrue.toString
      case (l1,l2) => s"[${l1} || ${l2}]"
    }

    override def toTex: String = s"${l1.toTex} \\vee ${l2.toTex}"

    override def lsVal: Set[PureVal] = l1.lsVal ++ l2.lsVal

    override def allMsg: Set[OAbsMsg] = l1.allMsg ++ l2.allMsg
  }
  case object LSTrue extends LSBexp {
    override def lsVar: Set[PureVar] = Set.empty
    override def contains(mt:MessageType,sig: Signature)(implicit ch:ClassHierarchyConstraints): Boolean = false

    override def swap(swapMap: Map[PureVar, PureExpr]) = this

    override def toString: String = "True"

    override def toTex: String = "\\enkwTrue"

    override def lsVal: Set[PureVal] = Set.empty

    override def allMsg: Set[OAbsMsg] = Set.empty
  }
  case object LSFalse extends LSBexp {
    override def lsVar: Set[PureVar] = Set.empty
    override def contains(mt:MessageType,sig: Signature)(implicit ch:ClassHierarchyConstraints): Boolean = false

    override def swap(swapMap: Map[PureVar, PureExpr]) = this

    override def toString: String = "False"

    override def toTex: String = "\\enkwFalse"

    override def lsVal: Set[PureVal] = Set.empty

    override def allMsg: Set[OAbsMsg] = Set.empty
  }

  /**
   * Has not or equals
   * Used to capture
   * @param v value quantified to this statement
   * @param m
   * @param extV ok if message arg matching v is equal to extV
   * @param constr
   */
  case class HNOE(v:PureVar, m:AbsMsg, extV:PureExpr) extends LSPred{
    override def toTex: String = ???

    override def swap(swapMap: Map[PureVar, PureExpr]): LSPred = {
      val swappedExtv = extV match{
        case pv:PureVar => swapMap.getOrElse(pv, pv)
        case v => v
      }

      HNOE(v, m.swap(swapMap), swappedExtv)
    }

    override def contains(mt: MessageType, sig: Signature)(implicit ch: ClassHierarchyConstraints): Boolean =
      m.contains(mt,sig)

    override def lsVar: Set[PureVar] = m.lsVar - v

    override def lsVal: Set[PureVal] = m.lsVal

    override def allMsg: Set[OAbsMsg] = Set(m.asInstanceOf[OAbsMsg])
  }

  sealed trait LSAtom extends LSPred {
//    def getAtomSig:String
    def identitySignature:String
  }
  object LSAtom{
    implicit val rw:RW[LSAtom] = RW.merge(NS.rw, LSSingle.rw)
  }

  sealed trait SignatureMatcher{
    /**
     * Testing method
     * @return an example of a signature that this would match
     */
    def example() :Signature

    def toTex(args:List[PureExpr]):String

    def matchesClass(sig: String):Boolean

    def matchesSubSig(subsig:String):Boolean
    def matches(sig:Signature)(implicit ch:ClassHierarchyConstraints):Boolean
    def identifier:String
  }
  object SignatureMatcher{
    implicit val rw:RW[SignatureMatcher] = RW.merge(SetSignatureMatcher.rw, SubClassMatcher.rw, ExactClassMatcher.rw)
  }
  @Deprecated
  case class SetSignatureMatcher(sigSet : Set[Signature]) extends SignatureMatcher {
    override def matches(sig: Signature)(implicit ch:ClassHierarchyConstraints): Boolean = sigSet.contains(sig)

    override def matchesSubSig(subsig: String): Boolean = sigSet.exists(v => subsig == v.methodSignature)

    private val sortedSig = sigSet.toList.sorted(SignatureOrdering)
    override def identifier: String =s"${sortedSig.head.base}_${sortedSig.head.methodSignature}"

    override def matchesClass(sig: String): Boolean = ???

    override def toTex(args:List[PureExpr]): String = ???

    /**
     * Testing method
     *
     * @return an example of a signature that this would match
     */
    override def example(): Signature = sigSet.head
  }
  object SetSignatureMatcher{
    implicit val rw:RW[SetSignatureMatcher] = macroRW
  }

  case class Signature(base:String, methodSignature:String){
    private var hashMem:Option[Int] = None
    override def hashCode(): Int = {
      if(hashMem.isEmpty){
        hashMem = Some(base.hashCode + methodSignature.hashCode)
      }
      hashMem.get
    }
    assert(!base.contains("("))
    assert(methodSignature.contains("("))
  }
  object Signature{
    implicit val rw:RW[Signature] = macroRW
    def apply(tup:(String,String)):Signature = Signature(tup._1,tup._2)
  }

  object SignatureOrdering extends Ordering[Signature] {
    override def compare(x: Signature, y: Signature): Int = {
      val baseComp = x.base.compareTo(y.base)
      if(baseComp != 0) baseComp
      else x.methodSignature.compareTo(y.methodSignature)
    }
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
    override def matches(sig: Signature)(implicit ch:ClassHierarchyConstraints): Boolean = {
      if(!matchesSubSig(sig.methodSignature)){
        return false
      }
      baseSubtypeOf.exists { bt =>
        if (ch.typeExists(bt)) { // Specs may not match any type if library has not been included in apk
          ch.getSubtypesOf(bt).contains(sig.base)
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

    /**
     * Quick and dirty method for generating example strings for regex used in unit testing
     * @param r some regular expression
     * @return a string that matches r if you are lucky (otherwise an exception)
     */
    /**
     * Testing method
     *
     * @return an example of a signature that this would match
     */
    override def example(): Signature = Signature(baseSubtypeOf.head, BounderUtil.exampleStringFromRegex(sigR))
  }
  object SubClassMatcher{
    def apply(baseSubtypeOf:String, signatureMatcher: String, ident:String):SubClassMatcher =
      SubClassMatcher(Set(baseSubtypeOf), signatureMatcher, ident)
    implicit val rw:RW[SubClassMatcher] = macroRW
  }

  case class ExactClassMatcher(baseMatcher:String, signatureMatcher:String, ident:String) extends SignatureMatcher{
    lazy val baseMatcherr = baseMatcher.r
    lazy val signatureMatcherr = signatureMatcher.r

    /**
     * Testing method
     *
     * @return an example of a signature that this would match
     */
    override def example(): Signature = Signature(BounderUtil.exampleStringFromRegex(baseMatcherr),
      BounderUtil.exampleStringFromRegex(signatureMatcherr))

    override def toTex(args: List[PureExpr]): String = ???

    override def matchesClass(sig: String): Boolean = baseMatcherr.matches(sig)

    override def matchesSubSig(subsig: String): Boolean = signatureMatcherr.matches(subsig)
    override def matches(sig: Signature)(implicit ch:ClassHierarchyConstraints): Boolean = {
      matchesSubSig(sig.methodSignature) && matchesClass(sig.base)
    }
    override def identifier: String = ident
  }
  object ExactClassMatcher{
    implicit val rw:RW[ExactClassMatcher] = macroRW

    val anyMethod = ExactClassMatcher(".*", ".*", "AnyMethod")
  }
  // A method with a signature in "signatures" has been invoed
  // lsVars: element 0 is return value, element 1 is reciever, rest of the elements are arguemnts
  // A string of "_" means "don't care"
  // primitives are parsed as in java "null", "true", "false", numbers etc.
  sealed trait LSSingle extends LSAtom {
    def lsVars: List[PureExpr]
  }
  object LSSingle{
    implicit val rw:RW[LSSingle] = RW.merge(OAbsMsg.rw, FreshRef.rw, CLInit.rw)
  }

  sealed trait AbsMsg extends LSSingle {

    def mt:MessageType
    def signatures:SignatureMatcher
    def lsVars:List[PureExpr]
    def copyMsg(lsVars: List[PureExpr]) :OAbsMsg = this match {
      case OAbsMsg(mt, signatures, _, isSynth) => OAbsMsg(mt, signatures, lsVars, isSynth)
    }

    override def swap(swapMap: Map[PureVar, PureExpr]): AbsMsg

    def mToTex: String
  }
  object AbsMsg{
    implicit val rw:RW[AbsMsg] = RW.merge(OAbsMsg.rw)

    def apply(mt:MessageType, signatures:SignatureMatcher, lsVars:List[PureExpr], isSynth:Boolean = false):OAbsMsg =
      OAbsMsg(mt, signatures, lsVars, isSynth)
  }

  case object AnyAbsMsg extends AbsMsg {
    override def mt: MessageType = ???

    override def signatures: SignatureMatcher = ???

    override def lsVars: List[PureExpr] = Nil


    override def mToTex: String = ???

    override def identitySignature: String = "AnyAbsMsg_______"

    override def toTex: String = ???

    override def contains(mt: MessageType, sig: Signature)(implicit ch: ClassHierarchyConstraints): Boolean = ???

    override def lsVar: Set[PureVar] = Set.empty

    override def swap(swapMap: Map[PureVar, PureExpr]): AbsMsg = this

    override def allMsg: Set[OAbsMsg] = Set.empty

    override def lsVal: Set[PureVal] = ???
  }


  case class OAbsMsg(mt: MessageType, signatures: SignatureMatcher, lsVars : List[PureExpr], isSynth:Boolean = false) extends AbsMsg {
    def cloneWithVar(v: PureVar, ind: Int, avoid:Set[PureVar]): OAbsMsg =
      this.copy(lsVars = lsVars.zipWithIndex.map{
        case (cpv, cInd) if cInd == ind => v
        case (cpv, _) => avoid.foldLeft(cpv.noCollide(v)){case (acc,v) => acc.noCollide(v)}
      })

    override def lsVar: Set[PureVar] = lsVars.flatMap {
      case pureVar: PureVar => Some(pureVar)
      case _: PureVal => None
    }.toSet

    def getVar(i: Int): PureExpr = lsVars(i)


    // Uesed for naming uninterpreted functions in z3 solver
    override def identitySignature: String = {
      // Note: this does not include varnames or
      // any other info that would distinguish this I from another with the same metods
      s"I_${mt.toString}_${BounderUtil.sanitizeString(signatures.identifier)}"
    }

    override def contains(omt:MessageType,sig: Signature)(implicit ch:ClassHierarchyConstraints): Boolean =
      omt == mt && signatures.matches(sig)

    override def swap(swapMap: Map[PureVar, PureExpr]): AbsMsg = {
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

    override def lsVal: Set[PureVal] = lsVars.flatMap{
      case v:PureVal => Some(v)
      case _ => None
    }.toSet

    override def allMsg: Set[OAbsMsg] = Set(this)
  }
  object OAbsMsg{
    implicit val rw:RW[OAbsMsg] = macroRW
  }
  // Since i1 has been invoked, i2 has not been invoked.
  case class NS(i1:AbsMsg, i2:AbsMsg) extends LSAtom{
    //assert(i2.lsVar.forall(x => i1.lsVar.contains(x)), "Free variables of i2 must be subset of free variables of i1")
    lazy val lsVar: Set[PureVar] = i1.lsVar.union(i2.lsVar)

//    override def getAtomSig: String = s"NI(${i1.getAtomSig}, ${i2.getAtomSig})"

    override def identitySignature: String = s"${i1.identitySignature}_${i2.identitySignature}"

    override def contains(mt:MessageType,sig: Signature)(implicit ch:ClassHierarchyConstraints): Boolean =
      i1.contains(mt, sig) || i2.contains(mt, sig)

    override def swap(swapMap: Map[PureVar, PureExpr]) = NS(i1.swap(swapMap), i2.swap(swapMap))

    override def toString: String = s"NS( $i1 , $i2 )"

    override def toTex: String = s"\\niDir{${i2.mToTex}}{${i1.mToTex}}"

    override def lsVal: Set[PureVal] = i1.lsVal ++ i2.lsVal

    override def allMsg: Set[OAbsMsg] = i1.allMsg ++ i2.allMsg
  }
  object NS{
    implicit val rw:RW[NS] = macroRW
  }
  case class LSSpec(univQuant:List[PureVar], existQuant:List[PureVar],
                    pred:LSPred, target: OAbsMsg, rhsConstraints: Set[LSConstraint] = Set()){

    def connectionCount(): Int = {
      def fact(n: Int): Int = {
        if (n < 1) 1 else fact(n - 1) * n
      }
      val msgs: List[OAbsMsg] = target :: EncodingTools.msgList(pred)
      val msgIndVar = msgs.flatMap{
        case m@OAbsMsg(_,_,args, _) => args.zipWithIndex.flatMap{
          case (v:PureVar,index) => Some((v,index,m))
          case _ => None
        }
      }
      val varUseGroups = msgIndVar.groupBy(v => v._1)
      varUseGroups.map{case (_, positions) =>
        if(positions.size > 1)
          fact(positions.size)
        else
          0 // if only one message mentions var then it is not "connected" to anything
      }.sum
    }



    def objCount(): Integer ={
      (LSPredAnyOrder.objectCount(target) ++ LSPredAnyOrder.objectCount(pred)).size
    }



    override def hashCode(): Int = {
      univQuant.## + existQuant.## + pred.## + target.##
    }
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
        target.copyMsg(lsVars = target.lsVars.map{
          case v2 if v2 == rhsConstraints.head.v1 => NullVal
          case v => v
        }).mToTex
      } else
        ???
      val out = s"\\specOnly{\\ensuremath{$tgtStr}}{\\ensuremath{${faQuant}${pred.toTex}}}"
      out
    }

    private def varNotQuantified(v:Set[PureVar]) = {
      throw new IllegalArgumentException(s"Mismatch between quantified variables and free variables.  " +
        s"Not quantified: ${v}")
    }
    private def checkWF(quant:Set[PureVar], p:LSPred):Boolean = p match {
      case LSConstraint(v1, _, v2:PureVar) =>
        val notContained = Set(v1,v2).diff(quant)
        if(notContained.nonEmpty)
          varNotQuantified(notContained)
        true
      case LSConstraint(v1, _, _) =>
        if(quant.contains(v1)) true else varNotQuantified(Set(v1))
      case Forall(vars, p) => checkWF(quant ++ vars,p)
      case Exists(vars, p) => checkWF(quant ++ vars,p)
      case LSImplies(l1, l2) => checkWF(quant,l1) && checkWF(quant,l2)
      case And(l1, l2) => checkWF(quant,l1) && checkWF(quant,l2)
      case Not(l) => checkWF(quant,l)
      case Or(l1, l2) => checkWF(quant,l1) && checkWF(quant,l2)
      case LSTrue => true
      case LSFalse => true
      case i:LSAtom =>
        val notContained = i.lsVar.diff(quant)
        if(notContained.nonEmpty)
          varNotQuantified(notContained)
        true
      //case UComb(_,preds,_) => preds.forall(p => checkWF(quant,p))
      case LSAnyPred => true
      case HNOE(v, m, otherV) => m.lsVars.count(_ == v) == 1 && v != otherV && m.lsVars.count(_==otherV) == 0
      case v =>
        throw new IllegalArgumentException(s"${v} is not a valid lspred")
    }
    private def checkWellFormed():Unit = {
      val quantified = univQuant.toSet ++ existQuant
      try {
        checkWF(quantified, pred)
        checkWF(quantified, target)
      }catch{
        case e:IllegalArgumentException =>
          println(this)
          throw e
      }
    }
    checkWellFormed()
    def instantiate(i:AbsMsg, specSpace: SpecSpace):LSPred = {
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

      val toSwap: Map[PureVar,PureExpr] = allPairs.flatMap{
        case (p1:PureVar, p2:PureVar) => Some(p1,p2)
        case (TopVal, _) => None
        case (_, TopVal) =>
          ???
        case (p1:PureVar, p2:PureExpr) => Some(p1,p2)
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
  def top:SpecSpace = new SpecSpace(Set())
  def allI(pred:Option[LSPred]):Set[OAbsMsg] = pred match {
    case Some(v) => allI(v)
    case None => Set()
  }
  def allPosI(pred:LSPred):Set[OAbsMsg] = pred match {
    case _:HNOE => Set.empty
    case LSImplies(l1, l2) => allI(l1).union(allI(l2))
    case CLInit(_) => Set()
    case i: OAbsMsg => Set(i)
    case NS(i1:OAbsMsg, _) => Set(i1)
    case NS(i1, _) => throw new IllegalArgumentException("malformed")
    case And(p1, p2) => allI(p1).union(allI(p2))
    case Or(p1, p2) => allI(p1).union(allI(p2))
    case Not(m:AbsMsg) => Set.empty
    case Not(p) => throw new IllegalArgumentException("General negation not allowed")
    case LSTrue => Set()
    case LSFalse => Set()
    case FreshRef(_) => Set()
    case Forall(_, p) => allI(p)
    case Exists(_, p) => allI(p)
    case LSConstraint(_, _, _) => Set()
    case LSAnyPred => Set()
  }
  def allI(pred:LSPred):Set[OAbsMsg] = pred match{
    case HNOE(_,m,_) => allI(m)
    case LSImplies(l1, l2) => allI(l1).union(allI(l2))
    case CLInit(_) => Set()
    case i:OAbsMsg => Set(i)
    case NS(i1,i2) => Set(i1,i2).flatMap{
      case o:OAbsMsg => Some(o)
      case _ => None
    }
    case And(p1,p2) => allI(p1).union(allI(p2))
    case Or(p1,p2) => allI(p1).union(allI(p2))
    case Not(p) => allI(p)
    case LSTrue => Set()
    case LSFalse => Set()
    case FreshRef(_) => Set()
    case Forall(_,p) => allI(p)
    case Exists(_,p) => allI(p)
    case LSConstraint(_,_, _) => Set()
    case LSAnyPred => Set()
  }
  def allI(spec:LSSpec, includeRhs:Boolean = true):Set[OAbsMsg] = spec match{
    case LSSpec(_,_,pred, target,_) if includeRhs => allI(pred).union(allI(target))
    case LSSpec(_,_,pred, target,_) => allI(pred)
  }
}


object LSPredAnyOrder{
//  private def comb(p1:LSPred, p2:LSPred):Option[Int] ={
//    (depthToAny(p1),depthToAny(p2)) match{
//      case (Some(v1), Some(v2)) => Some(Math.min(v1,v2))
//      case (Some(v), _) => Some(v)
//      case (_,o)  => o
//    }
//  }
  private def directCompare(pred1: LifeState.LSPred, pred2: LifeState.LSPred):Int =
    pred1.toString.compareTo(pred2.toString) // ensure deterministic order, probably don't care what order it is.

  def objectCount(p:LSPred):Set[PureVar] = p match {
    case OAbsMsg(_,_,lsVars, _) => lsVars.flatMap{
      case v:PureVar => Some(v)
      case _ => None
    }.toSet
    case NS(m1,m2) => objectCount(m1) ++ objectCount(m2)
    case Or(m1,m2) => objectCount(m1) ++ objectCount(m2)
    case And(m1,m2) => objectCount(m1) ++ objectCount(m2)
    case Not(m) => objectCount(m)
    case AnyAbsMsg => Set()
    case LSAnyPred => Set()
    case LSConstraint(v1,_,v2) => Set(v1,v2).flatMap {
      case v: PureVar => Some(v)
      case _ => None
    }
    case Forall(_, p) => objectCount(p)
    case Exists(_, p) => objectCount(p)
  }

  def depthToAny(p:LSPred):Int = p match {
    case NS(_, AnyAbsMsg) => 0
    case LSAnyPred => 0
    case Or(p1, p2) => Math.min(depthToAny(p1), depthToAny(p2))
    case And(p1, p2) => Math.min(depthToAny(p1), depthToAny(p2))
    case Not(p) => 999
    case Forall(vars, p) => depthToAny(p) + 1
    case Exists(vars, p) => depthToAny(p) + 1
    //TODO: find something better here, just needs to be bigger than everything without causing an overflow
    case _: LifeState.LSAtom => 999
  }
  def msgRank(m:AbsMsg): Double = m match{
    case OAbsMsg(mt, sig, vars,_) => 1 - (0.01 * vars.count(v => v.isInstanceOf[PureVar]))
    case AnyAbsMsg => 1 - 0.10
  }

  def predMsgCount(p: LSPred): Int = p match {
      case LSAnyPred => 0
      case Or(p1, p2) => predMsgCount(p1) + predMsgCount(p2)
      case And(p1, p2) => predMsgCount(p1) + predMsgCount(p2)
      case Not(p) => predMsgCount(p)
      case Forall(vars, p) => predMsgCount(p)
      case Exists(vars, p) => predMsgCount(p)
      case NS(AnyAbsMsg, AnyAbsMsg) => 0
      case NS(m1, m2:OAbsMsg) => 2
      case NS(m1, AnyAbsMsg) => 1
      case m: AbsMsg => 1
      case _: LifeState.LSAtom => 1
      case LSConstraint(_,_,_) => 0
    }
  def rankPred(p:LSPred):Double = {
    def comb(p1:LSPred, p2:LSPred, op:(Double,Double) => Double):Double = op(rankPred(p1) , rankPred(p2))
    p match {
      case LSAnyPred => 999
      case Or(p1, p2) => comb(p1,p2, _+_) + 1
      case And(p1, p2) => comb(p1,p2, _+_) + 1
      case Not(p) => rankPred(p) + 1
      case Forall(vars, p) => rankPred(p) + 1
      case Exists(vars, p) => rankPred(p) + 1
      case NS(m1,m2) => msgRank(m1) + msgRank(m2)
      case m:AbsMsg => msgRank(m)
//      case _:NS => 2
      case _: LifeState.LSAtom => 1
    }
  }
  def predDepth(p:LSPred):Int = p match {
    case LSAnyPred => 1
    case Or(p1, p2) => predDepth(p1) + predDepth(p2) + 1
    case And(p1, p2) => predDepth(p1) + predDepth(p2) + 1
    case Not(p:OAbsMsg) => 1
    case Forall(vars, p) => predDepth(p)
    case Exists(vars, p) => predDepth(p)
    case _: LifeState.LSAtom => 1
    case _:LSConstraint => 1
  }
  def predAnyCount(p:LSPred):Int = p match {
    case LSAnyPred => 1
    case NS(_,AnyAbsMsg) => 1
    case Or(p1, p2) => predAnyCount(p1) + predAnyCount(p2)
    case And(p1, p2) => predAnyCount(p1) + predAnyCount(p2)
    case Not(p: OAbsMsg) => 0
    case Forall(_, p) => predAnyCount(p)
    case Exists(_, p) => predAnyCount(p)
    case _: LifeState.LSAtom => 0
  }

  def hasAny(p: LSPred): Boolean = p match {
    case LSAnyPred => true
    case NS(_,AnyAbsMsg) => true

    case Or(p1, p2) => hasAny(p1) || hasAny(p2)
    case And(p1, p2) => hasAny(p1) || hasAny(p2)
    case Not(p: OAbsMsg) => hasAny(p)
    case Forall(_, p) => hasAny(p)
    case Exists(_, p) => hasAny(p)
    case _: LifeState.LSAtom => false
    case _:LSConstraint => false
  }

  def rankSpecSpace(x: SpecSpace): Int =
    x.getSpecs.toList.map { s => predDepth(s.pred) }.sum
  def countAny(p:SpecSpace):Int = {
    p.getSpecs.toList.map { s =>
      predAnyCount(s.pred)
    }.sum
  }

  val SpecSpaceAnyOrder = Ordering.by{(v:SpecSpace) =>
//    (countAny(v), rankSpecSpace(v), v.hashCode())
    (rankSpecSpace(v), v.hashCode()) //TODO:=== is this better?
  }.reverse //Note priority queue does highest first

  val SpecStepOrder = Ordering.by{(sp:LSSpec) =>
    (if(hasAny(sp.pred)) 0 else 1, depthToAny(sp.pred), sp.hashCode())}
}

/**
 * Representation of a set of possible lifestate specs
 * disallowSpecs are conditions that a method should not be invoked under (e.g. throwing an exception)
 * enableSpecs are conditions required for a callback or callin return
 * @matcherSpace additional matchers that may be used for synthesis (added to allI)
 **/
class SpecSpace(enableSpecs: Set[LSSpec], disallowSpecs:Set[LSSpec] = Set(),
                matcherSpace:Set[OAbsMsg] = Set(),
                searchProbOpt:Option[BigInt] = None, // always take one of n paths so only keep denominator of rational
                searchProbNaive:Option[BigInt]= None,
                searchSteps:Option[BigInt] = None,
                createMissingI:Boolean = false
               ) {

  private val cachedPureVals = {
    (enableSpecs ++ disallowSpecs).flatMap{l => SpecSpace.allI(l)}.flatMap{m => m.lsVal} ++
      matcherSpace.flatMap{m => m.lsVal}
  }
  def getPureVals:Set[PureVal] = cachedPureVals
  def getSearchSteps:BigInt = {
    assert(searchSteps.isDefined, "search steps must be defined")
    searchSteps.get
  }
  /**
   * Only call if known to be defined
   * @return
   */
  def getSearchProbOpt:BigInt = {
    assert(searchProbOpt.isDefined, "probability must be defined to be gotten")
    searchProbOpt.get
  }

  def getSearchProbNaive: BigInt = {
    assert(searchProbNaive.isDefined, "probability must be defined to be gotten")
    searchProbNaive.get
  }

  def setProbNaive(i: BigInt): SpecSpace =
    new SpecSpace(enableSpecs, disallowSpecs, matcherSpace, searchProbOpt, searchProbNaive=Some(i), searchSteps)

  def setProbOpt(i: BigInt) =
    new SpecSpace(enableSpecs, disallowSpecs, matcherSpace, searchProbOpt = Some(i), searchProbNaive, searchSteps)

  def setSearchSteps(i: BigInt) =
    new SpecSpace(enableSpecs, disallowSpecs, matcherSpace, searchProbOpt, searchProbNaive, searchSteps = Some(i))

  override def hashCode(): Int = {
    (enableSpecs.map{s => s.hashCode()} ++ disallowSpecs.map{s => s.hashCode()}).hashCode()
  }
  def stats(): Map[String,Double] = {
    val allSpecs = enableSpecs.toList ++ disallowSpecs.toList
    val specMessageCount = allSpecs.map{s => LSPredAnyOrder.predMsgCount(s.pred)}
    val objectCount:Integer = allSpecs.map{s => s.objCount()}.foldLeft(0){
      case (acc,v) => acc + v
    }
    val connectionCount = allSpecs.map{s => s.connectionCount()}.sum
    Map(
      "total messages" ->
        specMessageCount.sum,
      "messagesPerSpec" -> specMessageCount.sum.toDouble / allSpecs.size.toDouble,
      "object count" -> objectCount.toDouble,
      "connection count" -> connectionCount,
      "spec count" -> (enableSpecs.size + disallowSpecs.size).toDouble,
      "matcher space" -> matcherSpace.size.toDouble,
      "search steps" -> getSearchSteps.toDouble,
      "probability optimized" -> getSearchProbOpt.toDouble,
      "probability naive" -> getSearchProbNaive.toDouble
    )
  }

  override def toString: String = {
    val builder = new StringBuilder()
    builder.append("enableSpecs\n------\n")
    enableSpecs.foreach(s => builder.append(s"${s.toString}\n"))
    builder.toString
  }

  def zip(other:SpecSpace):Set[(LSSpec, LSSpec)] = {
    val matched = mutable.HashSet[LSSpec]()
    matched.addAll(other.getSpecs)
    def matchWith(spec:LSSpec, other:SpecSpace):(LSSpec, LSSpec) = {
      val otherSpecs = other.specsByI(spec.target).filter(_.target == spec.target)
      assert(otherSpecs.size < 2 ,"Should only be one spec for each target.")
      if(otherSpecs.isEmpty){
        // if no other spec exists in other, then it is the same as "true"
        (spec, spec.copy(pred = LSTrue))
      }else{
        val otherSpec = otherSpecs.head
        matched.remove(otherSpec)
        (spec,otherSpec)
      }
    }

    enableSpecs.map{mySpec =>
      matchWith(mySpec, other)
    } ++ matched.map{otherSpec =>
      val (a,b) = matchWith(otherSpec,this)
      (b,a)
    }
  }

  def copy(enableSpecs:Set[LSSpec] = this.enableSpecs,
           disallowSpecs:Set[LSSpec] = this.disallowSpecs,
           matcherSpace:Set[OAbsMsg] = this.matcherSpace
          ):SpecSpace = new SpecSpace(enableSpecs, disallowSpecs, matcherSpace,
    searchProbOpt = searchProbOpt, searchProbNaive = searchProbNaive, searchSteps = searchSteps)

  def findIFromCurrent(dir: MessageType, signature: Signature,  lst : Option[List[Option[RVal]]] = None)(implicit cha:ClassHierarchyConstraints):Set[OAbsMsg] = {
    val found = allI.filter(i => i.mt == dir && i.signatures.matches(signature))

    if(dir == CIEnter && found.isEmpty){ // Don't bother with ci enter for artificial msg
      return found
    }

    if(!createMissingI || found.nonEmpty || lst.isEmpty) found else {
      val matcher = SubClassMatcher(signature.base, signature.methodSignature.replace("(", "\\(").replace(")","\\)"),
        s"synth_${signature.base}${signature.methodSignature}")
      Set(AbsMsg(dir, matcher ,lst.get.zipWithIndex.map{case ( _,ind) => if (ind == 1) RelevantNotDefined else BotVal}, isSynth = true))
    }
  }

  def specsByI(i: AbsMsg) = {
    val ids = i.identitySignature
    val specs = enableSpecs.filter(spec => spec.target.identitySignature == ids)
    specs
  }
  def disSpecsByI(i:AbsMsg) = {
    val ids = i.identitySignature
    val disSpecs = disallowSpecs.filter(spec => spec.target.identitySignature == ids)
    disSpecs
  }

  private var allIMemo:Option[Set[OAbsMsg]] = None
  def allI:Set[OAbsMsg] ={
    if(allIMemo.isEmpty)
      allIMemo = Some((enableSpecs ++ disallowSpecs).flatMap{spec =>
        SpecSpace.allI(spec.pred) + spec.target
      } ++ matcherSpace)
    allIMemo.get
  }

  def getSpecs:Set[LSSpec] = enableSpecs
  def getDisallowSpecs:Set[LSSpec] = disallowSpecs
  def getMatcherSpace:Set[OAbsMsg] = matcherSpace

  /**
   * For step back over a place where the code may emit a message find the applicable I and assign fresh ls vars.
   * Return has arbitrary non-top pure expr for arguments that matter, top for ones that don't.
   * Caller must replace all non-top pure expr with something from abstract state.
   * @param mt Direction of message
   * @param sig class name and method signature (e.g. void foo(java.lang.Object))
   * @return Some(I) if I exists, None otherwise.
   */
  def getIWithMergedVars(mt: MessageType, sig: Signature, lst : Option[List[Option[RVal]]] = None)
                        (implicit ch : ClassHierarchyConstraints):Option[AbsMsg] = {
    //    iset.get(mt,sig).map{i =>
    //      i.copy(lsVars = i.lsVars.map(a => if(a != "_") nextFreshLSVar() else "_"))
    //    }
    def merge(v:(PureExpr,PureExpr)):PureExpr = v match{
      case (TopVal,v) => v
      case (v,_) => v
    }
    var solverSig:Option[String] = None
    val normFiltered: Set[OAbsMsg] = allI.filter{ i =>
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
    val out = if(normFiltered.nonEmpty) normFiltered else findIFromCurrent(mt, sig, lst)
    if(out.isEmpty)
      return None

    // Compute intersection of defined variables
    val parList = out.foldLeft(List():List[PureExpr]){
      case (acc,OAbsMsg(_,_,vars, _)) =>
        acc.zipAll(vars,TopVal,TopVal).map(merge)
    }

    val headSig = out.headOption.map(i => i.identitySignature)
    assert(out.tail.forall(i => headSig.forall(v => v == i.identitySignature)),
      "All matched i must have same identity signature")
    out.headOption.map(v => v.copyMsg(lsVars = parList))
  }


  /**
   * Find a lifestate spec by
   *
   * @param pkg
   * @param name
   * @return
   */
  def specsBySig(mt: MessageType, sig:Signature)(implicit ch: ClassHierarchyConstraints):Set[LSSpec] = {
    var solverSig:Option[String] = None
    val out: Set[OAbsMsg] = allI.filter{ i =>
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
    val specsForSig = enableSpecs.filter(a => a.target.mt == mt && a.target.signatures.matches(sig))
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

