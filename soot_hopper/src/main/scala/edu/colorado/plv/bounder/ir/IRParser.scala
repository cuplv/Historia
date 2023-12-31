package edu.colorado.plv.bounder.ir
import scala.util.parsing.combinator._


sealed trait TRef{
  def sootString:String
}
case class ClazzRef(pkg:List[String], name:String) extends TRef {
  override def sootString: String = pkg.mkString(".") + s".$name"
}
case class InterfaceRef(pkg:List[String], name:String) extends TRef{
  override def sootString: String = pkg.mkString(".") + s".$name"
}

case class PrimRef(p:String)extends TRef{
  override def sootString: String = p
}
case class ArrayRef(r:TRef) extends TRef{
  override def sootString:String = r.sootString + "[]"
}

object IRParser{
  val parser = new IRParser
  def parseReflectiveRef(ref:String):TRef = {
    val res = parser.parseAll(parser.reflectiveRef, ref)
    res.getOrElse(throw new IllegalArgumentException(s"Failed to parse reflective type reference: $ref"))
  }
}

class IRParser extends RegexParsers{

  //TODO: This duplicates soot.dexpler.Util.dottedClassName

  def decl : Parser[String] = ("L" | "I")
  def arrayDecl : Parser[String] = ("[")
  def primitive :Parser[TRef] = ("C" | "Z" | "B" | "S" | "I" | "D" | "J" | "D" | "F" | "V") ^^ {
    case "J" => PrimRef("long")
    case "S" => PrimRef("short")
    case "D" => PrimRef("double")
    case "I" => PrimRef("int")
    case "F" => PrimRef("float")
    case "B" => PrimRef("byte")
    case "C" => PrimRef("char")
    case "Z" => PrimRef("boolean")
    case "V" => PrimRef("void")
  } //TODO: probably more prim types
//  def intPrimitive :Parser[TRef] = "I" ^^ {case "I" => PrimRef("int")}

  def identifier : Parser[String] = """[a-zA-Z][a-zA-Z0-9$_]*""".r ^^ {a=>a}
  def reflectiveQualifiedName: Parser[List[String]] =
    identifier ~ ";" ^^ {case v ~ _ => v::Nil} |
      identifier ~ "/" ~ reflectiveQualifiedName ^^ {case v ~ _ ~ l => v::l}

  def reflectiveRef: Parser[TRef] = (arrayReflectiveRef | baseReflectiveRef | primitive)

  def baseReflectiveRef: Parser[TRef] = {
    decl ~ reflectiveQualifiedName ^^ {
      case "L" ~ l =>
        val rev = l.reverse
        ClazzRef(rev.tail.reverse, l.last)
      case "I" ~ l  =>
        val rev = l.reverse
        InterfaceRef(rev.tail.reverse, l.last)
    }
  }

  def arrayReflectiveRef:Parser[TRef] =
    arrayDecl ~ reflectiveRef ^^ {
      case _ ~ r => ArrayRef(r)
    }
}
