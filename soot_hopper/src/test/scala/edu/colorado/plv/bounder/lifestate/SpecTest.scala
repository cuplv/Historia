package edu.colorado.plv.bounder.lifestate

import edu.colorado.plv.bounder.BounderSetupApplication
import edu.colorado.plv.bounder.ir.JimpleFlowdroidWrapper
import edu.colorado.plv.bounder.lifestate.LifeState.I
import edu.colorado.plv.bounder.symbolicexecutor.state.Qry
import edu.colorado.plv.bounder.symbolicexecutor.{ControlFlowResolver, DefaultAppCodeResolver, PatchedFlowdroidCallGraph, SymbolicExecutorConfig, TransferFunctions}
import org.scalatest.funsuite.AnyFunSuite
import soot.{Scene, SootMethod}

import scala.jdk.CollectionConverters.CollectionHasAsScala

class SpecTest extends AnyFunSuite {
  def findIInFwk[M, C](i: I): Boolean = {
    val signatures = i.signatures
    val matching = signatures.filter{
      case (clazz, method) =>
        if (Scene.v().containsClass(clazz)) {
          val sootClass = Scene.v().getSootClass(clazz)
          val res = sootClass.declaresMethod(method)
          res
        } else false
    }
    println(s"spec $i matches the following classes:")
    matching.foreach(sig => println(s"    $sig"))
    matching.nonEmpty
  }
  def findIInFwkForall[M, C](i: I):Unit= {
    val signatures = i.signatures
    val matching = signatures.foreach {
      case (clazz, method) =>
        if (Scene.v().containsClass(clazz)) {
          val sootClass = Scene.v().getSootClass(clazz)
          val res = sootClass.declaresMethod(method)
          assert(res, s"""class : "$clazz" , method: "$method" not found in framework""")
        } else assert(false, s"class: $clazz not in framework")
    }
  }

  test("Each I in spec signatures corresponds to a method or interface in the framework"){
    val apk = getClass.getResource("/Antennapod-fix-2856-app-free-debug.apk").getPath
    assert(apk != null)
    BounderSetupApplication.loadApk(apk, PatchedFlowdroidCallGraph)

    assert(findIInFwk(SpecSignatures.Activity_onPause_entry))
    assert(findIInFwk(SpecSignatures.Activity_init_exit))
    assert(findIInFwk(SpecSignatures.Activity_onResume_exit))
    assert(findIInFwk(SpecSignatures.Activity_onPause_exit))
    assert(findIInFwk(SpecSignatures.Activity_onResume_entry))
    findIInFwkForall(SpecSignatures.Fragment_get_activity_exit_null)
    findIInFwkForall(SpecSignatures.Fragment_onActivityCreated_entry)
    findIInFwkForall(SpecSignatures.Fragment_onDestroy_exit)

  }

  test("Dummy test to print framework types"){
    val apk = getClass.getResource("/Antennapod-fix-2856-app-free-debug.apk").getPath
    assert(apk != null)
    BounderSetupApplication.loadApk(apk, PatchedFlowdroidCallGraph)
    val w = new JimpleFlowdroidWrapper(apk,PatchedFlowdroidCallGraph)
    val a = new DefaultAppCodeResolver[SootMethod, soot.Unit](w)
    val frameworkMethods = Scene.v().getClasses.asScala.flatMap{clazz =>
      val clazzname = JimpleFlowdroidWrapper.stringNameOfClass(clazz)
      if(a.isFrameworkClass(clazzname))
        clazz.getMethods.asScala.map(method => (clazzname, method.getSubSignature, method))
      else Nil
    }

    printMatchingSignatures("Fragment","getActivity",frameworkMethods, isCallin = true)
    printMatchingSignatures("Fragment","onActivityCreated",frameworkMethods, isCallin = false)
    printMatchingSignatures("Fragment","onDestroy",frameworkMethods, isCallin = false)

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
