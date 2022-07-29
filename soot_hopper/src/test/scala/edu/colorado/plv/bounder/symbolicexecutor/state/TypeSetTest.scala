package edu.colorado.plv.bounder.symbolicexecutor.state

import edu.colorado.plv.bounder.ir.{BitTypeSet, TypeSet}
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, SetInclusionTypeSolving, StateTypeSolving, Z3StateSolver}
import org.scalatest.funsuite.AnyFunSuite

import scala.collection.BitSet

class TypeSetTest extends AnyFunSuite {
  val hierarchy: Map[String, Set[String]] =
    Map("java.lang.Object" -> Set("String", "Foo", "Bar","Baz",
      "java.lang.Object"),
      "String" -> Set("String"), "Foo" -> Set("Bar", "Foo","Baz"), "Bar" -> Set("Bar"),
      "java.lang.Runnable" -> Set("Bar","Baz", "java.lang.Runnable"),
      "Baz" -> Set("Baz")
    )
  private val classToInt: Map[String, Int] = hierarchy.keySet.zipWithIndex.toMap
  val intToClass: Map[Int, String] = classToInt.map(k => (k._2, k._1))

  object BoundedTypeSet {
    def apply(someString: Some[String], none: None.type, value: Set[Nothing]): TypeSet = someString match{
      case Some(v) =>
        val types = hierarchy(v).map(classToInt)
        val bitSet = BitSet() ++ types
        BitTypeSet(bitSet)
    }
  }
  private def getCha() : ClassHierarchyConstraints= {


    val pc = new ClassHierarchyConstraints(hierarchy,Set("java.lang.Runnable"),intToClass)
    pc
  }
  // TODO: write tests for other type set
  test("Subtype constrains type set"){
    // Subtype restricts type set
//    implicit val cha = getCha()
//    val ts = BoundedTypeSet(Some("Foo"),None,Set())
//    assert(ts.typeSet(cha) == Set("Foo","Bar","Baz"))
//
//    // Interface restricts type set
//    val ts2 = ts.copy(interfaces = Set("java.lang.Runnable"))
//    assert(ts2.typeSet(cha) == Set("Bar","Baz"))
//
//    val ts3 = ts.copy(lower=Some("Foo"))
//    assert(ts3.typeSet(cha) == Set("Foo"))
//
//    val ts4 = DisjunctTypeSet(Set(ts, BoundedTypeSet(Some("String"), None,Set())))
//    assert(ts4.typeSet(cha) == Set("Foo","Bar","Baz","String"))
//
//    val ts5 = ts4.setInterfaces(Set("java.lang.Runnable"))
//    assert(ts5.typeSet(cha) == Set("Bar","Baz"))
//
//    val ts6 = ts4.constrainSubtypeOf("String",cha)
//    assert(ts6.typeSet(cha) == Set("String"))
//
//    val ts7 = ts4.constrainSupertypeOf("Bar",cha)
//    assert(ts7.typeSet(cha) == Set("Bar","Foo"))
//
//    // contains
//    assert(ts.contains(ts))
//
//    assert(ts.contains(BoundedTypeSet(Some("Foo"),Some("Foo"),Set())))
//    assert(ts.contains(BoundedTypeSet(Some("Baz"),None,Set())))
//
//    assert(ts4.contains(BoundedTypeSet(Some("String"),None,Set())))
//
//    val empty:TypeSet = EmptyTypeSet
//    assert(!empty.contains(ts4))
//
//    assert(!ts4.contains(BoundedTypeSet(Some("java.lang.Object"),None,Set())))
//
//    assert(ts4.constrainSubtypeOf("Bar",cha).typeSet(cha) == Set("Bar"))
  }
}
