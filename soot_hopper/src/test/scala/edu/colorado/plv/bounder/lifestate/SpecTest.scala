package edu.colorado.plv.bounder.lifestate

import edu.colorado.plv.bounder.BounderSetupApplication
import edu.colorado.plv.bounder.ir.{CIEnter, CIExit, JimpleFlowdroidWrapper}
import edu.colorado.plv.bounder.lifestate.LifeState.{I, SubClassMatcher}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.{CHACallGraph, DefaultAppCodeResolver, PatchedFlowdroidCallGraph, SparkCallGraph, SymbolicExecutorConfig, TransferFunctions}
import org.scalatest.funsuite.AnyFunSuite
import soot.{Scene, SootMethod}

import scala.jdk.CollectionConverters.CollectionHasAsScala

class SpecTest extends AnyFunSuite {
  def findIInFwk[M, C](i: I)(implicit ch:ClassHierarchyConstraints): Boolean = {
//    val signatures = i.signatures
//    val matching = signatures.filter{
//      case (clazz, method) =>
//        if (Scene.v().containsClass(clazz)) {
//          val sootClass = Scene.v().getSootClass(clazz)
//          val res = sootClass.declaresMethod(method)
//          res
//        } else false
//    }
//    println(s"spec $i matches the following classes:")
//    matching.foreach(sig => println(s"    $sig"))
//    matching.nonEmpty
    Scene.v().getClasses.asScala.exists{ c =>
      c.getMethods.asScala.exists{m =>
        i.signatures.matches((c.getName, m.getSubSignature))
      }
    }
  }
//  def findIInFwkForall[M, C](i: I):Unit= {
//    val signatures = i.signatures
//    val matching = signatures.foreach {
//      case (clazz, method) =>
//        if (Scene.v().containsClass(clazz)) {
//          val sootClass = Scene.v().getSootClass(clazz)
//          val res = sootClass.declaresMethod(method)
//          assert(res, s"""class : "$clazz" , method: "$method" not found in framework""")
//        } else assert(false, s"class: $clazz not in framework")
//    }
//  }

  test("Should parse I and match subtypes") {
    implicit val ch = new ClassHierarchyConstraints(Map(
      "rx.Single" -> Set("rx.Single","otherthing"),
      "Runnable" -> Set("MyRunnable")
    ), Set("Runnable"))
    val i1 = LifeState.parseI("""I(ci [_, v, _] foobar foo(java.lang.List, _ ) v<:rx.Single )""")
    assert(i1.mt == CIEnter)
    assert(i1.signatures.matches(("rx.Single","foobar foo(java.lang.List, int)")))
    assert(i1.signatures.matches(("otherthing","foobar foo(java.lang.List, Bundle)")))
    assert(!i1.signatures.matches(("MyRunnable","foobar foo(java.lang.List, Bundle)")))
    val i2 = LifeState.parseI("I(ciret [_,v,_] rx.Subscription subscribe(rx.functions.Action1) v<:rx.Single)")
    assert(i2.mt == CIExit)
    val i3 = LifeState.parseI("I(ciret [_,v,_] rx.Subscription\n subscribe(rx.functions.Action1) v<:rx.Single)")
    assert(i3.mt == CIExit)

    //|$SUB = I(ciret [_,v,_] rx.Subscription subscribe(rx.functions.Action1) v<:rx.Single);
    //
    //|NI($SUB,$SUB)
    //|   <= $SUB ;
//    val ifile =
//      """
//        | I(ciret [_,v,_] rx.Subscription subscribe(rx.functions.Action1) v<:rx.Single)
//        |  <= I(ciret [_,v,_] rx.Subscription subscribe(rx.functions.Action1) v<:rx.Single);
//        |""".stripMargin
//    val i4 = LifeState.parseSpec(ifile)
//    println(i4)
//    val i5 = LifeState.parseSpec("\n")
//    assert(i5.isEmpty)

  }
  test("Antennapod: Each I in spec signatures corresponds to a method or interface in the framework"){
    val apk = getClass.getResource("/Antennapod-fix-2856-app-free-debug.apk").getPath
    assert(apk != null)
    val w = new JimpleFlowdroidWrapper(apk,SparkCallGraph, Set())
    val transfer =  (cha:ClassHierarchyConstraints) =>
      new TransferFunctions[SootMethod,soot.Unit](w, new SpecSpace(Set()),cha)
    val config = SymbolicExecutorConfig(
      stepLimit = 8, w,transfer, printProgress = true)
    val symbolicExecutor = config.getSymbolicExecutor
    implicit val ch = w.getClassHierarchyConstraints

    assert(findIInFwk(SpecSignatures.Activity_onPause_entry))
    assert(findIInFwk(SpecSignatures.Activity_init_exit))
    assert(findIInFwk(SpecSignatures.Activity_onResume_exit))
    assert(findIInFwk(SpecSignatures.Activity_onPause_exit))
    assert(findIInFwk(SpecSignatures.Activity_onResume_entry))
//    assert(findIInFwk(SpecSignatures.Fragment_get_activity_exit_null
//      .copy(signatures = SpecSignatures.Fragment_getActivity_Signatures
//        .filter(a => a._1 != "androidx.fragment.app.Fragment" ))))
    assert(findIInFwk(SpecSignatures.Fragment_onActivityCreated_entry))
    assert(findIInFwk(SpecSignatures.Fragment_onDestroy_exit))
//    findIInFwkForall(SpecSignatures.RxJava_call_entry)
    assert(findIInFwk(SpecSignatures.RxJava_unsubscribe_exit))
  }
  test("RXJavaSubscribe: Each I in spec signatures corresponds to a method or interface in the framework"){
    val apk = getClass.getResource("/RXJavaSubscribe-fix-debug.apk").getPath
    assert(apk != null)
    val w = new JimpleFlowdroidWrapper(apk,SparkCallGraph, Set())
    val transfer =  (cha:ClassHierarchyConstraints) =>
      new TransferFunctions[SootMethod,soot.Unit](w, new SpecSpace(Set()),cha)
    val config = SymbolicExecutorConfig(
      stepLimit = 8, w,transfer, printProgress = true)
    val symbolicExecutor = config.getSymbolicExecutor
    implicit val ch = w.getClassHierarchyConstraints
//    BounderSetupApplication.loadApk(apk, CHACallGraph)

//    findIInFwkForall(SpecSignatures.Fragment_get_activity_exit_null
//      .copy(signatures = SpecSignatures.Fragment_getActivity_Signatures
//        .filter(a => a._1 == "androidx.fragment.app.Fragment" )))

    assert(findIInFwk(SpecSignatures.Fragment_onActivityCreated_entry))
    assert(findIInFwk(SpecSignatures.Fragment_onDestroy_exit))
    assert(findIInFwk(SpecSignatures.Fragment_onDestroy_exit))
  }

  test("Dummy test to print framework types"){
    val apk = getClass.getResource("/RXJavaSubscribe-fix-debug.apk").getPath
    assert(apk != null)
    BounderSetupApplication.loadApk(apk, SparkCallGraph)
    val w = new JimpleFlowdroidWrapper(apk,SparkCallGraph, Set())
    val a = new DefaultAppCodeResolver[SootMethod, soot.Unit](w)
    val frameworkMethods = Scene.v().getClasses.asScala.flatMap{clazz =>
      val clazzname = JimpleFlowdroidWrapper.stringNameOfClass(clazz)
      if(a.isFrameworkClass(clazzname))
        clazz.getMethods.asScala.map(method => (clazzname, method.getSubSignature, method))
      else Nil
    }

    printMatchingSignatures("rx","unsubscribe",frameworkMethods, isCallin = false)
  }

  private def printMatchingSignatures(classContains: String,
                                      nameContains:String,
                                      frameworkMethods: Iterable[(String, String,SootMethod)], isCallin:Boolean) = {
    val filtered = frameworkMethods.filter { m =>
      m._1.contains(classContains) && m._2.contains(nameContains) && (isCallin || !m._3.isFinal)
    }
    println(s"=== clazz: $classContains === name: $nameContains")
    filtered.foreach(sig => println(s"""("${sig._1}","${sig._2}"),"""))
  }
}
