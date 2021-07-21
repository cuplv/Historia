package edu.colorado.plv.bounder.lifestate

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{CBEnter, CBExit, CIEnter, CIExit, MessageType}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, I, LSFalse, LSPred, LSSpec, LSTrue, LifeStateParser, NI, Not, Or, Ref}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.state.{BoolVal, CmpOp, Equals, NotEquals, NullVal, PureExpr, PureVal, PureVar, Subtype}

import scala.util.parsing.combinator._
import upickle.default.{macroRW, ReadWriter => RW}

import scala.util.matching.Regex


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
      case "<:" => Subtype
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
      case _ ~ pmDir ~ _ ~ vars ~ _ ~ ret ~ sName ~ _ ~ para ~ _ ~ LSConstraint(v1, Subtype, v2) ~ _ =>
        assert(vars.size < 2 || vars(1) == "_" || vars(1) == v1, "Can only specify receiver type in I")
        val p = para.map(rf)
        val sigRegex = rf(ret) +" " + sName + "\\(" +  p.mkString(",") + "\\)"
        val ident = ret + "__" + sName + "__" + p.mkString("___")
        val scm = SubClassMatcher(v2, sigRegex, ident)
        I(pmDir, scm, vars)
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
  }

  sealed trait LSPred {
    def swap(swapMap: Map[String, String]):LSPred

    def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints):Boolean

    def lsVar: Set[String]
  }
  object LSPred{
    implicit var rw:RW[LSPred] = RW.merge(LSAtom.rw, macroRW[Not], macroRW[And],
      macroRW[Or], macroRW[LSTrue.type], macroRW[LSFalse.type])
  }
//  case class LSEq(v1:String,v2:String) extends LSPred {
//    override def swap(swapMap: Map[String, String]): LSPred =
//    {
//      def swapIfVar(v: String):String = v match{
//        case LSVar(v2) => swapMap(v2)
//        case v2 => v2
//      }
//      LSEq(swapIfVar(v1), swapIfVar(v2))
//    }
//
//    override def contains(mt: MessageType, sig: (String, String))(implicit ch: ClassHierarchyConstraints): Boolean =
//      false
//
//    override def lsVar: Set[String] = Set(v1,v2).filter(v => LSVar.matches(v))
//  }

  /**
   * Trace references value.
   * V must be referenced in trace so far for Ref(V) to hold.
   * Not(Ref(V)) means V cannot appear in past trace
   * @param v
   */
  case class Ref(v: String) extends LSSingle {
    override def contains(mt: MessageType, sig: (String, String))(implicit ch: ClassHierarchyConstraints): Boolean =
      false

    override def lsVar: Set[String] = if(v == "_") Set() else Set(v)

    override def identitySignature: String = ???

    override def lsVars: List[String] = lsVar.toList

    override def swap(swapMap: Map[String, String]): LifeState.Ref = {
      assert(swapMap.contains(v), "Swap must contain all variables")
      Ref(swapMap(v))
    }
  }
  object Ref{
    private def oneCont(a1:LSPred, a2:LSPred):Option[Ref] = {
      val a1_ = containsRefV(a1)
      lazy val a2_ = containsRefV(a2)
      if(a1_.isEmpty) a2_ else a1_
    }
    def containsRefV(a: LSPred):Option[Ref] = a match{
      case v@Ref(_) => Some(v)
      case Not(a) => containsRefV(a)
      case And(a1,a2) => oneCont(a1,a2)
      case Or(a1,a2) => oneCont(a1,a2)
      case LSTrue => None
      case LSFalse => None
      case _:NI => None
      case _:I => None
    }

    implicit var rw:RW[Ref] = macroRW
  }

  val LSGenerated = "LS_GENERATED_.*".r

  case class And(l1 : LSPred, l2 : LSPred) extends LSPred {
    override def lsVar: Set[String] = l1.lsVar.union(l2.lsVar)
    override def toString:String = s"(${l1.toString} AND ${l2.toString})"

    override def contains(mt:MessageType, sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean =
      l1.contains(mt,sig) || l2.contains(mt,sig)

    override def swap(swapWithFresh: Map[String, String]): LSPred =
      And(l1.swap(swapWithFresh), l2.swap(swapWithFresh))
  }
  case class Not(l: LSPred) extends LSPred {
    override def lsVar: Set[String] = l.lsVar
    override def toString:String = s"(NOT ${l.toString})"

    override def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean =
      l.contains(mt,sig)

    override def swap(swapMap: Map[String, String]): LSPred = Not(l.swap(swapMap))
  }
  case class Or(l1:LSPred, l2:LSPred) extends LSPred {
    override def lsVar: Set[String] = l1.lsVar.union(l2.lsVar)
    override def toString:String = s"(${l1.toString} OR ${l2.toString})"
    override def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean =
      l1.contains(mt, sig) || l2.contains(mt,sig)

    override def swap(swapMap: Map[String, String]): LSPred = Or(l1.swap(swapMap), l2.swap(swapMap))
  }
  case object LSTrue extends LSPred {
    override def lsVar: Set[String] = Set.empty
    override def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean = false

    override def swap(swapMap: Map[String, String]): LSPred = this
  }
  case object LSFalse extends LSPred {
    override def lsVar: Set[String] = Set.empty
    override def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean = false

    override def swap(swapMap: Map[String, String]): LSPred = this
  }

  sealed trait LSAtom extends LSPred {
//    def getAtomSig:String
    def identitySignature:String
  }
  object LSAtom{
    implicit val rw:RW[LSAtom] = RW.merge(NI.rw, LSSingle.rw)
  }

  sealed trait SignatureMatcher{
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
    def lsVars: List[String] //==========
  }
  object LSSingle{
    implicit val rw:RW[LSSingle] = RW.merge(I.rw, Ref.rw)
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
    override def toString:String = s"I($mt $identitySignature ( ${lsVars.mkString(",")} )"

    override def contains(omt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean =
      omt == mt && signatures.matches(sig)

    override def swap(swapMap: Map[String, String]): I = {
      val newLSVars = lsVars.map{v =>
        assert(swapMap.contains(v), s"SwapMap must contain v: ${v}")
        swapMap(v)
      }
      this.copy(lsVars = newLSVars)
    }
  }
  object I{
    implicit val rw:RW[I] = macroRW
  }
  // Since i1 has been invoked, i2 has not been invoked.
  case class NI(i1:I, i2:I) extends LSAtom{
    def lsVar: Set[String] = i1.lsVar.union(i2.lsVar)

//    override def getAtomSig: String = s"NI(${i1.getAtomSig}, ${i2.getAtomSig})"

    override def identitySignature: String = s"${i1.identitySignature}_${i2.identitySignature}"
    override def toString:String = s"NI( ${i1.toString} , ${i2.toString} )"

    override def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean =
      i1.contains(mt, sig) || i2.contains(mt, sig)

    override def swap(swapMap: Map[String, String]): LSPred = NI(i1.swap(swapMap), i2.swap(swapMap))
  }
  object NI{
    implicit val rw:RW[NI] = macroRW
  }
  case class LSSpec(pred:LSPred, target: I, rhsConstraints: Set[LSConstraint] = Set()){
    def instantiate(i:I, specSpace: SpecSpace):LSPred = {
      val swap = (target.lsVars zip i.lsVars).filter{
        case (LSAnyVal(),_) => false
        case (_,LSAnyVal()) => false
        case _ => true
      }
      val unbound = pred.lsVar -- swap.map(_._1)
      val swapWithFresh = (swap ++ unbound.map(v => (v,specSpace.nextFreshLSVar()))).toMap
      val swappedPred = pred.swap(swapWithFresh)
      val swappedRhs = rhsConstraints.map(_.swap(swapWithFresh))
      if(rhsConstraints.isEmpty)
        swappedPred
      else {
        And(swappedPred, swappedRhs.reduce(And))
      }
    }
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
    case i@I(_,_,_) => Set(i)
    case NI(i1,i2) => Set(i1,i2)
    case And(p1,p2) => allI(p1).union(allI(p2))
    case Or(p1,p2) => allI(p1).union(allI(p2))
    case Not(p) => allI(p)
    case LSTrue => Set()
    case LSFalse => Set()
    case Ref(_) => Set()
  }
  def allI(spec:LSSpec, includeRhs:Boolean = true):Set[I] = spec match{
    case LSSpec(pred, target,_) if includeRhs => allI(pred).union(allI(target))
    case LSSpec(pred, target,_) => allI(pred)
  }
}
/**
 * Representation of a set of possible lifestate specs */
class SpecSpace(enableSpecs: Set[LSSpec], disallowSpecs:Set[LSSpec] = Set()) {
  def specsByI(i: I) = {
    val ids = i.identitySignature
    val specs = enableSpecs.filter(spec => spec.target.identitySignature == ids)
    specs
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


  private var freshLSVarIndex = 0
  def nextFreshLSVar():String = {
    val ind = freshLSVarIndex
    freshLSVarIndex = freshLSVarIndex+1
    s"LS_GENERATED__${ind}"
  }
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
    val out: Set[I] = allISpecs.getOrElse(mt,Set()).filter{ i =>
      if(i.signatures.matches(sig)) {
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
    val parListFresh = parList.map(a => if(a!="_") nextFreshLSVar() else "_")

    val headSig = out.headOption.map(i => i.identitySignature)
    assert(out.tail.forall(i => headSig.forall(v => v == i.identitySignature)),
      "All matched i must have same identity signature")
//    assert(out.size == 1 || out.isEmpty, "I must be unique for each message")
    //copy I with intersection of defined vars
    out.headOption.map(v => v.copy(lsVars = parListFresh))
  }
  def getRefWithFreshVars(): Ref ={
    Ref(nextFreshLSVar())
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

