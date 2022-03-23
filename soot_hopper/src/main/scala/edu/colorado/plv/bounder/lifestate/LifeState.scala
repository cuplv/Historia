package edu.colorado.plv.bounder.lifestate

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{CBEnter, CBExit, CIEnter, CIExit, MessageType}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, CLInit, Exists, Forall, FreshRef, I, LSConstraint, LSFalse, LSImplies, LSPred, LSSpec, LSTrue, LifeStateParser, NI, Not, Or}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.state.{BoolVal, CmpOp, Equals, NotEquals, NullVal, PureExpr, PureVal, PureVar, State}

import scala.util.parsing.combinator._
import upickle.default.{macroRW, ReadWriter => RW}

import scala.util.matching.Regex

object LSVarGen{
  private var next = 0

  def setNext(states:List[State]):Unit = {

    states.foreach{s =>
      val mv = s.sf.traceAbstraction.modelVars.keySet ++ s.sf.traceAbstraction.rightOfArrow.flatMap {
        case CLInit(sig) => Set()
        case FreshRef(v) => Set(v)
        case I(mt, signatures, lsVars) => lsVars
      }
      mv.map{
        case n if n.startsWith("LS__") && n.drop(4).toInt >= next =>
          next = n.drop(4).toInt
        case _ =>
      }
    }
  }
  def getNext:String = {
    next = next + 1
    s"LS__${next}"
  }
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
    case class AstMac(id:AstID, i:I) extends Line
    case class AstRule(v1:Ast, tgt:AstID) extends Line
    // TODO: identifier should handle arrays, for now use java.util.List_ instead of java.util.List[]
    def identifier: Parser[String] = """[a-zA-Z][a-zA-Z0-9$_.]*""".r ^^ { a => a }

    def macroIdentifier:Parser[AstID] = """#[a-zA-Z][a-zA-Z0-9_]*""".r ^^ {
      case ident => AstID(ident.drop(1))
    }

    def astMac:Parser[AstMac] = macroIdentifier ~ "=" ~ i ^^{
      case id ~ _ ~ lhs => AstMac(id, lhs)
    }

    //parse everything except I
    def lsRule :Parser[AstRule] = ???

    // parse I
    def empty: Parser[String] = "_"

    def parMatcher:Parser[String] = identifier | empty //TODO: and const

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
    }
    def constr:Parser[LSConstraint] = identifier ~ op ~ identifier ^^ {
      case id1 ~ op ~ id2 =>
        LSConstraint(id1, op, id2)

    }
    def constrs:Parser[List[LSConstraint]] = repsep(constr,sep)

    def lsVarList:Parser[List[String]] = repsep(parMatcher,",")

    def params = repsep(parMatcher, ",")

    def rf(v:String):String = v.replace("_","[^,()]*")

    def i: Parser[I] = "I(" ~ mDir ~ "[" ~ lsVarList ~"]" ~ identifier ~ identifier ~"(" ~ params ~ ")" ~ constr ~ ")" ^^ {
//      case _ ~ pmDir ~ _ ~ vars ~ _ ~ ret ~ sName ~ _ ~ para ~ _ ~ LSConstraint(v1, Subtype, v2) ~ _ =>
//        assert(vars.size < 2 || vars(1) == "_" || vars(1) == v1, "Can only specify receiver type in I")
//        val p = para.map(rf)
//        val sigRegex = rf(ret) +" " + sName + "\\(" +  p.mkString(",") + "\\)"
//        val ident = ret + "__" + sName + "__" + p.mkString("___")
//        val scm = SubClassMatcher(v2, sigRegex, ident)
//        I(pmDir, scm, vars)
      case _ => throw new IllegalArgumentException("Can only specify receiver type in I")
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
  def parseI(str:String):I = {
    val res: LifeStateParser.ParseResult[I] = LifeStateParser.parseAll(LifeStateParser.i, str)
    if(res.successful)
      res.get
    else
      throw new IllegalArgumentException(res.toString)
  }
  def parseIFile(str:String):Seq[I] = {
    str.split("\n").filter(v => !v.trim.startsWith("#") && !(v.trim == "")).map(parseI)
  }

  def parseSpec(str:String):Set[LSSpec] = {
    val withoutComments = str.split("\n").filter{v => !v.trim.startsWith("#") && !v.trim.isEmpty }.mkString("\n")
    if(withoutComments == ""){
      return Set() // This is dumb, I shouldn't need to do this
    }
    val lines = withoutComments.split(";").map(_.trim).filter(_ != "")
    val res = lines.map(line => {
      val lineRes = LifeStateParser.parseAll(???, line)
      if (lineRes.successful) {
        lineRes.get
      } else throw new IllegalStateException(lineRes.toString)
    })
    res.toSet
  }

  var id = 0
  def nextLsVar():String = {
    val lsVar = "v" + id
    id = id+1
    lsVar
  }

  // Const value matchers
  val LSBoolConst = "@(false|true|False|True)".r
  val LSNullConst = "@(?:null|Null|NULL)".r
  object LSConst{
    def unapply(arg: String): Option[PureVal] = arg match{
      case LSBoolConst(sv) => Some(BoolVal(sv.toBoolean))
      case LSNullConst() => Some(NullVal)
      case _ => None
    }
  }
  val LSVar = "((?:[a-zA-Z])(?:[a-zA-Z0-9]|_)*)".r
  val SynthLSVar = "LS_(\\d*)".r


  val LSAnyVal = "_".r

  case class LSConstraint(v1:String,op:CmpOp,v2:String ) extends LSPred {
    override def swap(swapMap: Map[String, String]): LSPred = {
      def swapIfVar(v: String):String = v match{
        case LSVar(v2) => swapMap(v2)
        case v2 => v2
      }
      LSConstraint(swapIfVar(v1),op, swapIfVar(v2))
    }
    override def contains(mt: MessageType, sig: (String, String))(implicit ch: ClassHierarchyConstraints): Boolean =
      false

    override def lsVar: Set[String] = Set(v1,v2).filter(v => LSVar.matches(v))

    override def stringRep(varMap: String => Any): String = s"[ ${varMap(v1)} == ${varMap(v2)} ]"

    override def toTex: String = op match {
      case Equals => s"${arg2tex(v1)} = ${arg2tex(v2)}"
      case NotEquals =>s"${arg2tex(v1)} \\neq ${arg2tex(v2)}"
    }
  }

  sealed trait LSPred {
    def toTex:String

    def swap(swapMap: Map[String, String]):LSPred

    def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints):Boolean

    def lsVar: Set[String]

    def stringRep(varMap : String => Any):String
  }
  object LSPred{
    implicit var rw:RW[LSPred] = RW.merge(LSAtom.rw, macroRW[Forall], macroRW[Exists], macroRW[Not], macroRW[And],
      macroRW[Or], macroRW[LSTrue.type], macroRW[LSFalse.type])
  }

  case class Forall(vars:List[String], p:LSPred) extends LSPred{
//    override def toString:String =
//      if(vars.isEmpty) p.toString else s"Forall([${vars.mkString(",")}], ${p.toString})"
    override def toTex: String = ???
    override def swap(swapMap: Map[String, String]): LSPred =
      Forall(vars.map(swapMap), p.swap(swapMap))

    override def contains(mt: MessageType, sig: (String, String))(implicit ch: ClassHierarchyConstraints): Boolean = ???

    override def lsVar: Set[String] = p.lsVar

    override def stringRep(varMap: String => Any): String =
      if(vars.nonEmpty)
        s"Ɐ ${vars.map(varMap).mkString(",")} . $p"
      else
        p.stringRep(varMap)
  }

  case class Exists(vars:List[String], p:LSPred) extends LSPred {
//    override def toString:String =
//      if(vars.isEmpty) p.toString else s"Exists([${vars.mkString(",")}],${p.toString})"
    override def swap(swapMap: Map[String, String]): LSPred =
      Exists(vars.map(swapMap), p.swap(swapMap))

    override def contains(mt: MessageType, sig: (String, String))(implicit ch: ClassHierarchyConstraints): Boolean = ???

    override def lsVar: Set[String] = p.lsVar
    override def stringRep(varMap: String => Any): String =
      if(vars.nonEmpty)
        s"∃ ${vars.map(varMap).mkString(",")} . ${p.stringRep(varMap)}"
      else
        p.stringRep(varMap)

    override def toTex: String = ???
  }

  case class CLInit(sig:String) extends LSSingle {
    override def lsVars: List[String] = Nil

    override def identitySignature: String =
      throw new IllegalStateException("No valid identity signature for CLInit")

    override def swap(swapMap: Map[String, String]): LSPred = this

    override def contains(mt: MessageType, sig: (String, String))(implicit ch: ClassHierarchyConstraints): Boolean =
      false

    override def lsVar: Set[String] = Set()

    override def stringRep(varmap: String => Any): String = this.toString

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
  case class FreshRef(v: String) extends LSSingle {
    override def contains(mt: MessageType, sig: (String, String))(implicit ch: ClassHierarchyConstraints): Boolean =
      false

    override def lsVar: Set[String] = if(v == "_") Set() else Set(v)

    override def identitySignature: String = s"FreshRef($v)"

    override def lsVars: List[String] = lsVar.toList

    override def swap(swapMap: Map[String, String]): LifeState.FreshRef = {
      assert(swapMap.contains(v), "Swap must contain all variables")
      FreshRef(swapMap(v))
    }

    override def stringRep(varmap: String => Any): String = this.toString

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
      case _:NI => None
      case _:I => None
    }

    implicit var rw:RW[FreshRef] = macroRW
  }

  val LSGenerated = "LS_.*".r

  case class LSImplies(l1:LSPred, l2:LSPred) extends LSPred{
    override def swap(swapMap: Map[String, String]): LSPred = LSImplies(l1.swap(swapMap), l2.swap(swapMap))

    override def contains(mt: MessageType, sig: (String, String))(implicit ch: ClassHierarchyConstraints): Boolean =
      l1.contains(mt,sig) || l2.contains(mt,sig)

    override def lsVar: Set[String] = l1.lsVar.union(l2.lsVar)

    override def stringRep(varmap: String => Any): String = s"[ ${l1.stringRep(varmap)} ➡ ${l1.stringRep(varmap)} ]"

    override def toTex: String = ???
  }
  case class And(l1 : LSPred, l2 : LSPred) extends LSPred {
    override def lsVar: Set[String] = l1.lsVar.union(l2.lsVar)
    override def toString:String = s"(${l1.toString} AND ${l2.toString})"

    override def contains(mt:MessageType, sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean =
      l1.contains(mt,sig) || l2.contains(mt,sig)

    override def swap(swapWithFresh: Map[String, String]): LSPred =
      And(l1.swap(swapWithFresh), l2.swap(swapWithFresh))

    override def stringRep(varMap: String => Any): String = (l1,l2) match {
      case (LSFalse, _) => LSFalse.stringRep(varMap)
      case (_, LSFalse) => LSFalse.stringRep(varMap)
      case (LSTrue, l) => l.stringRep(varMap)
      case (l, LSTrue) => l.stringRep(varMap)
      case (l1,l2) => s"[ ${l1.stringRep(varMap)} && ${l2.stringRep(varMap)} ]"
    }

    override def toTex: String = s"${l1.toTex} \\wedge ${l2.toTex}"
  }
  case class Not(l: LSPred) extends LSPred {
    override def lsVar: Set[String] = l.lsVar
    override def toString:String = s"(NOT ${l.toString})"

    override def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean =
      l.contains(mt,sig)

    override def swap(swapMap: Map[String, String]): LSPred = Not(l.swap(swapMap))

    override def stringRep(varMap: String => Any): String = s"¬${l.stringRep(varMap)}"

    override def toTex: String = l match {
      case i: I=> s"\\notiDir{${i.mToTex}}"
      case _ => ??? //s"\\neg ${l.toTex}"
    }
  }
  case class Or(l1:LSPred, l2:LSPred) extends LSPred {
    override def lsVar: Set[String] = l1.lsVar.union(l2.lsVar)
    override def toString:String = s"(${l1.toString} OR ${l2.toString})"
    override def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean =
      l1.contains(mt, sig) || l2.contains(mt,sig)

    override def swap(swapMap: Map[String, String]): LSPred = Or(l1.swap(swapMap), l2.swap(swapMap))

    override def stringRep(varMap: String => Any): String = (l1, l2) match {
      case (LSFalse, l) => l.stringRep(varMap)
      case (l, LSFalse) => l.stringRep(varMap)
      case (LSTrue, _) => LSTrue.stringRep(varMap)
      case (_, LSTrue) => LSTrue.stringRep(varMap)
      case (l1,l2) => s"[${l1.stringRep(varMap)} || ${l2.stringRep(varMap)}]"
    }

    override def toTex: String = s"${l1.toTex} \\vee ${l2.toTex}"
  }
  case object LSTrue extends LSPred {
    override def lsVar: Set[String] = Set.empty
    override def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean = false

    override def swap(swapMap: Map[String, String]): LSPred = this

    override def stringRep(varMap: String => Any): String = "True"

    override def toTex: String = "\\enkwTrue"
  }
  case object LSFalse extends LSPred {
    override def lsVar: Set[String] = Set.empty
    override def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean = false

    override def swap(swapMap: Map[String, String]): LSPred = this

    override def stringRep(varMap: String => Any): String = "False"

    override def toTex: String = "\\enkwFalse"
  }

  sealed trait LSAtom extends LSPred {
//    def getAtomSig:String
    def identitySignature:String
  }
  object LSAtom{
    implicit val rw:RW[LSAtom] = RW.merge(NI.rw, LSSingle.rw)
  }

  sealed trait SignatureMatcher{
    def toTex(args:List[String]):String

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

    override def toTex(args:List[String]): String = ???
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


    override def toTex(argsin:List[String]): String = {
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
    def lsVars: List[String]
  }
  object LSSingle{
    implicit val rw:RW[LSSingle] = RW.merge(I.rw, FreshRef.rw, CLInit.rw)
  }
  case class I(mt: MessageType, signatures: SignatureMatcher, lsVars : List[String]) extends LSSingle {
    def constVals(constraints: Set[LSConstraint]):List[Option[(CmpOp, PureExpr)]] = lsVars.map{
      case LifeState.LSConst(v) => Some((Equals, v))
      case LifeState.LSVar(v) =>
        constraints.find(c => c.v1 == v || c.v2 == v) match {
          case Some(LSConstraint(_, op, LifeState.LSConst(v2))) => Some(op,v2)
          case Some(LSConstraint(LifeState.LSConst(v1), op, _)) => Some(op,v1)
          case None => None
          case c => throw new IllegalStateException(s"Malformed constraint: $c")
        }
      case _ => None
    }
//    private val sortedSig = signatures.toList.sorted
    override def lsVar: Set[String] = lsVars.filter(vname => LifeState.LSVar.matches(vname)).toSet

    def getVar(i: Int): String = lsVars(i)


//    override def getAtomSig: String = {
//      s"I(${sortedSig.mkString(":")})"
//    }

    // Uesed for naming uninterpreted functions in z3 solver
    override def identitySignature: String = {
      // Note: this does not include varnames or
      // any other info that would distinguish this I from another with the same metods
      s"I_${mt.toString}_${signatures.identifier}"
    }
    override def toString:String = stringRep(a => a)

    override def contains(omt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean =
      omt == mt && signatures.matches(sig)

    override def swap(swapMap: Map[String, String]): I = {
      val newLSVars = lsVars.map{
        case LSVar(v) =>
          swapMap.getOrElse(v,v)
        case c => c
      }
      this.copy(lsVars = newLSVars)
    }

    override def stringRep(varMap: String => Any): String =
      s"I($mt $identitySignature ( ${lsVars.map(varMap).mkString(",")} )"

    def mToTex:String = s"${mt.toTex}~${signatures.toTex(lsVars)}"

    override def toTex: String = s"\\iDir{${mToTex}}" //TODO:====
  }
  object I{
    implicit val rw:RW[I] = macroRW
  }
  // Since i1 has been invoked, i2 has not been invoked.
  case class NI(i1:I, i2:I) extends LSAtom{
    def lsVar: Set[String] = i1.lsVar.union(i2.lsVar)

//    override def getAtomSig: String = s"NI(${i1.getAtomSig}, ${i2.getAtomSig})"

    override def identitySignature: String = s"${i1.identitySignature}_${i2.identitySignature}"
    override def toString:String = stringRep(a => a)

    override def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean =
      i1.contains(mt, sig) || i2.contains(mt, sig)

    override def swap(swapMap: Map[String, String]): LSPred = NI(i1.swap(swapMap), i2.swap(swapMap))

    override def stringRep(varMap: String => Any): String = s"NI( ${i1.stringRep(varMap)} , ${i2.stringRep(varMap)} )"

    override def toTex: String = s"\\niDir{${i2.mToTex}}{${i1.mToTex}}"
  }
  object NI{
    implicit val rw:RW[NI] = macroRW
  }
  case class LSSpec(univQuant:List[String], existQuant:List[String],
                    pred:LSPred, target: I, rhsConstraints: Set[LSConstraint] = Set()){
    def toTex():String = {
      // in paper language, universal quantification of target vars is implicit
      val dispUnivQuant = univQuant.toSet -- target.lsVar

      val faQuant = if(dispUnivQuant.nonEmpty) s"\\forall ${dispUnivQuant.mkString(",")}." else ""
      // existential quantification of matcher variables is implicit
      // val exQuant = if(existQuant.nonEmpty) s"\\exists ${existQuant.mkString(",")}." else ""
      val tgtStr = if(rhsConstraints.isEmpty)
        target.mToTex
      else if(rhsConstraints.exists{
        case LSConstraint(v, Equals, LSNullConst()) => true
        case _ => false
      }) {
        target.copy(lsVars = target.lsVars.map{
          case v2 if v2 == rhsConstraints.head.v1 => "@null"
          case v => v
        }).mToTex
      } else
        ???
      val out = s"\\specOnly{\\ensuremath{$tgtStr}}{\\ensuremath{${faQuant}${pred.toTex}}}"
      out
    }

    private def checkWF(quant:Set[String], p:LSPred):Boolean = p match {
      case LSConstraint(v1, _, v2) => quant.contains(v1) && quant.contains(v2)
      case Forall(vars, p) => checkWF(quant ++ vars,p)
      case Exists(vars, p) => checkWF(quant ++ vars,p)
      case LSImplies(l1, l2) => checkWF(quant,l1) && checkWF(quant,l2)
      case And(l1, l2) => checkWF(quant,l1) && checkWF(quant,l2)
      case Not(l) => checkWF(quant,l)
      case Or(l1, l2) => checkWF(quant,l1) && checkWF(quant,l2)
      case LSTrue => true
      case LSFalse => true
      case i:LSAtom => i.lsVar.forall(v => quant.contains(v))
      case v =>
        throw new IllegalArgumentException(s"${v} is not a valid lspred")
    }
    private def checkWellFormed():Unit = {
      val quantified = univQuant.toSet ++ existQuant
      if(!(checkWF(quantified, pred) && checkWF(quantified,target)))
        throw new IllegalArgumentException("mismatch between quantified variables and free variables")
    }
    checkWellFormed()
    def instantiate(i:I, specSpace: SpecSpace):LSPred = {
      val swap = (target.lsVars zip i.lsVars).filter{
        case (LSAnyVal(),_) => false
        case (_,LSAnyVal()) => false
        case _ => true
      }
      val existingLSVars = swap.map(v => v._2).toSet
      val unbound = pred.lsVar -- swap.map(_._1)

      val swapWithFresh = (swap ++ unbound.map{v =>
//        val nextFresh = specSpace.nextFreshLSVar()
        val nextFresh = LSVarGen.getNext
        if(existingLSVars.contains(nextFresh)) //TODO: remove dbg code
          assert(!existingLSVars.contains(nextFresh),
            "Duplicate lsvar, if in unit test, call nextFreshLSVar a few times")
        (v,nextFresh)
      }).toMap
      val swappedPred = pred.swap(swapWithFresh)
      val swappedRhs = rhsConstraints.map(_.swap(swapWithFresh))

      // Quantify variables not in the target
      val newUnivQuant = univQuant.toSet -- swap.map(_._1)


      val lsFormula = if(rhsConstraints.isEmpty)
        swappedPred
      else {
        LSImplies(swappedRhs.reduce(And),swappedPred)
      }
//      assert(newUnivQuant.isEmpty, "TODO: is it ever the case that this is not empty on examples before " +
//        "the click specification?") //TODO: remaining forall here seems to cause timeout issues
      Forall(newUnivQuant.toList.map(swapWithFresh), Exists(existQuant.map(swapWithFresh), lsFormula))

    }
  }

  def arg2tex(v: String): String = v match {
    case LSVar(v) => v
    case LSNullConst() => "\\enkwNull"
    case LSBoolConst(v) if v.contains("rue") => "\\enkwTrue"
    case LSBoolConst(v) if v.contains("alse") => "\\enkwFalse"
    case LSAnyVal() => "_"
    case _ =>
      ???
  }

  // Class that holds a graph of possible predicates and alias relations between the predicates.
  // Generated from a fast pre analysis of the applications.
  // Set of vars that can alias are represented by having the same name.
  class PredicateSpace(predicates: Set[LSAtom]){
    /** mapping from variable names to predicates containing variable */
    val findVars: Map[String, Set[LSAtom]] = predicates.foldLeft(Map[String, Set[LSAtom]]()) { (acc, v) =>
      v.lsVar.foldLeft(acc){ (iacc, varname) => iacc + (varname -> (iacc.getOrElse(varname, Set()) + v) )}
    }

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
  def allI(pred:Option[LSPred]):Set[I] = pred match {
    case Some(v) => allI(v)
    case None => Set()
  }
  def allI(pred:LSPred):Set[I] = pred match{
    case LSImplies(l1, l2) => allI(l1).union(allI(l2))
    case CLInit(_) => Set()
    case i@I(_,_,_) => Set(i)
    case NI(i1,i2) => Set(i1,i2)
    case And(p1,p2) => allI(p1).union(allI(p2))
    case Or(p1,p2) => allI(p1).union(allI(p2))
    case Not(p) => allI(p)
    case LSTrue => Set()
    case LSFalse => Set()
    case FreshRef(_) => Set()
    case Forall(_,p) => allI(p)
    case Exists(_,p) => allI(p)
    case LSConstraint(_,_, _) => Set()
  }
  def allI(spec:LSSpec, includeRhs:Boolean = true):Set[I] = spec match{
    case LSSpec(_,_,pred, target,_) if includeRhs => allI(pred).union(allI(target))
    case LSSpec(_,_,pred, target,_) => allI(pred)
  }
}
/**
 * Representation of a set of possible lifestate specs */
class SpecSpace(enableSpecs: Set[LSSpec], disallowSpecs:Set[LSSpec] = Set()) {
  def findIFromCurrent(dir: MessageType, signature: (String, String))(implicit cha:ClassHierarchyConstraints):Set[I] = {
    allI.filter(i => i.mt == dir && i.signatures.matches(signature))
  }

  def specsByI(i: I) = {
    val ids = i.identitySignature
    val specs = enableSpecs.filter(spec => spec.target.identitySignature == ids)
    specs
  }
  def disSpecsByI(i:I) = {
    val ids = i.identitySignature
    val disSpecs = disallowSpecs.filter(spec => spec.target.identitySignature == ids)
    disSpecs
  }

  private var allIMemo:Option[Set[I]] = None
  def allI:Set[I] ={
    if(allIMemo.isEmpty)
      allIMemo = Some((enableSpecs ++ disallowSpecs).flatMap{spec =>
        SpecSpace.allI(spec.pred) + spec.target
      })
    allIMemo.get
  }

  def getSpecs:Set[LSSpec] = enableSpecs
  private val allISpecs: Map[MessageType, Set[I]] =
    (enableSpecs ++ disallowSpecs).flatMap(SpecSpace.allI(_)).groupBy(i => i.mt)


//  private var freshLSVarIndex = 0
//  def nextFreshLSVar():String = {
//    val ind = freshLSVarIndex
//    freshLSVarIndex = freshLSVarIndex+1
//    s"LS__${ind}"
//  }
  /**
   * For step back over a place where the code may emit a message find the applicable I and assign fresh ls vars.
   * Fresh LS vars are generated for vars and constants
   * @param mt Direction of message
   * @param sig class name and method signature (e.g. void foo(java.lang.Object))
   * @return Some(I) if I exists, None otherwise.
   */
  def getIWithFreshVars(mt: MessageType, sig: (String, String))(implicit ch : ClassHierarchyConstraints):Option[I] = {
    //    iset.get(mt,sig).map{i =>
    //      i.copy(lsVars = i.lsVars.map(a => if(a != "_") nextFreshLSVar() else "_"))
    //    }
    def merge(v:(String,String)):String = v match{
      case ("_",v) => v
      case (v,_) => v
    }
    var solverSig:Option[String] = None
    val out: Set[I] = allI.filter{ i =>
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
    val parList = out.foldLeft(List():List[String]){
      case (acc,I(_,_,vars)) =>
        acc.zipAll(vars,"_","_").map(merge)
    }
    val parListFresh = parList.map(a => if(a!="_") LSVarGen.getNext else "_")

    val headSig = out.headOption.map(i => i.identitySignature)
    assert(out.tail.forall(i => headSig.forall(v => v == i.identitySignature)),
      "All matched i must have same identity signature")
//    assert(out.size == 1 || out.isEmpty, "I must be unique for each message")
    //copy I with intersection of defined vars
    out.headOption.map(v => v.copy(lsVars = parListFresh))
  }
  def getRefWithFreshVars(): FreshRef ={
    FreshRef(LSVarGen.getNext)
  }

  /**
   * Find a lifestate spec by
   *
   * @param pkg
   * @param name
   * @return
   */
  def specsBySig(mt: MessageType, pkg:String, name:String)(implicit ch: ClassHierarchyConstraints):Set[LSSpec] = {
    // TODO: cache specs in hash map
    val getI = getIWithFreshVars(mt, (pkg,name)).map(_.identitySignature)
    val specsForSig = enableSpecs.filter(a => a.target.mt == mt && a.target.signatures.matches((pkg,name)))
    val identSigs: Set[String] = specsForSig.map(_.target.identitySignature) ++ getI
    identSigs.reduceOption((a:String,b:String) => {
      assert(a == b, s"Mismatched identity signatures: ${a} and ${b}")
      a
    })
    specsForSig
  }

}

