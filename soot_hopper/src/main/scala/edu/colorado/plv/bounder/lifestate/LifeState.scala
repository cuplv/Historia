package edu.colorado.plv.bounder.lifestate

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{CBEnter, CBExit, CIEnter, CIExit, MessageType}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, I, LSFalse, LSPred, LSSpec, LSTrue, LifeStateParser, NI, Not, Or}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.state.{BoolVal, CmpOp, Equals, NotEquals, NullVal, PureExpr, PureVal, Subtype}

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

  case class LSConstraint(v1:String,op:CmpOp,v2:String )

  sealed trait LSPred {
    def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints):Boolean

    def lsVar: Set[String]
  }
  object LSPred{
    implicit var rw:RW[LSPred] = RW.merge(LSAtom.rw, macroRW[Not], macroRW[And],
      macroRW[Or], macroRW[LSTrue.type], macroRW[LSFalse.type])
  }

  val LSGenerated = "LS_GENERATED_.*".r

  case class And(l1 : LSPred, l2 : LSPred) extends LSPred {
    override def lsVar: Set[String] = l1.lsVar.union(l2.lsVar)
    override def toString:String = s"(${l1.toString} AND ${l2.toString})"

    override def contains(mt:MessageType, sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean =
      l1.contains(mt,sig) || l2.contains(mt,sig)
  }
  case class Not(l: LSPred) extends LSPred {
    override def lsVar: Set[String] = l.lsVar
    override def toString:String = s"(NOT ${l.toString})"

    override def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean =
      l.contains(mt,sig)
  }
  case class Or(l1:LSPred, l2:LSPred) extends LSPred {
    override def lsVar: Set[String] = l1.lsVar.union(l2.lsVar)
    override def toString:String = s"(${l1.toString} OR ${l2.toString})"
    override def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean =
      l1.contains(mt, sig) || l2.contains(mt,sig)
  }
  case object LSTrue extends LSPred {
    override def lsVar: Set[String] = Set.empty
    override def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean = false
  }
  case object LSFalse extends LSPred {
    override def lsVar: Set[String] = Set.empty
    override def contains(mt:MessageType,sig: (String, String))(implicit ch:ClassHierarchyConstraints): Boolean = false
  }

  sealed trait LSAtom extends LSPred {
//    def getAtomSig:String
    def identitySignature:String
  }
  object LSAtom{
    implicit val rw:RW[LSAtom] = RW.merge(I.rw, NI.rw)
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
  case class I(mt: MessageType, signatures: SignatureMatcher, lsVars : List[String]) extends LSAtom {
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
  }
  object NI{
    implicit val rw:RW[NI] = macroRW
  }
  sealed trait LSMacroAndSpec
  case class LSSpec(pred:LSPred, target: I, rhsConstraints: Set[LSConstraint] = Set()) extends LSMacroAndSpec

  case class MacroID(name:String) extends LSAtom {
    // Parser should substitute all of these
    override def identitySignature: String =
      throw new IllegalStateException()

    override def contains(mt: MessageType, sig: (String, String))(implicit ch: ClassHierarchyConstraints): Boolean =
      throw new IllegalStateException()

    override def lsVar: Set[String] =
      throw new IllegalStateException()
  }
  case class LSMacro(name:MacroID, pred:LSPred) extends LSMacroAndSpec

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
  def allI(pred:LSPred):Set[I] = pred match{
    case i@I(_,_,_) => Set(i)
    case NI(i1,i2) => Set(i1,i2)
    case And(p1,p2) => allI(p1).union(allI(p2))
    case Or(p1,p2) => allI(p1).union(allI(p2))
    case Not(p) => allI(p)
    case LSTrue => Set()
    case LSFalse => Set()
  }
  def allI(spec:LSSpec, includeRhs:Boolean = true):Set[I] = spec match{
    case LSSpec(pred, target,_) if includeRhs => allI(pred).union(allI(target))
    case LSSpec(pred, target,_) => allI(pred)
  }
}
/**
 * Representation of a set of possible lifestate specs */
class SpecSpace(specs: Set[LSSpec]) {
  def getSpecs:Set[LSSpec] = specs
  private val allISpecs: Map[MessageType, Set[I]] = specs.flatMap(SpecSpace.allI(_)).groupBy(i => i.mt)


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
    allISpecs.getOrElse(mt,Set()).find(i => i.signatures.matches(sig)).map{ i =>
      i.copy(lsVars = i.lsVars.map(a => if(a != "_") nextFreshLSVar() else "_"))
    }
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
    val specsForSig = specs.filter(a => a.target.mt == mt && a.target.signatures.matches((pkg,name)))
    specsForSig
  }

}

