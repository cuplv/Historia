package edu.colorado.plv.bounder.lifestate

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{CBEnter, CBExit, CIEnter, CIExit}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, I, LSFalse, LSSpec, NI, Not, Or}
import edu.colorado.plv.bounder.symbolicexecutor.state.{Equals, NotEquals}

object SpecSignatures {

  // TODO: parse specs from DSL
  // TODO: type constraints on runtime value of LS vars instead of syntactic matching of signature
  //    e.g. the following would eliminate the need for enumerating activity types
  //    I(void onActivityCreated(), _::a, a<:Activity)
  val activityTypeSet = Set(
    "androidx.appcompat.app.AppCompatActivity",
    "androidx.fragment.app.FragmentActivity",
    "androidx.core.app.ComponentActivity",
    "android.app.Activity",
  )

  // Activity lifecycle
  val Activity_onResume_entry = I(CBEnter, activityTypeSet.map((_, "void onResume()")), List("_", "a"))
  val Activity_onResume_exit = I(CBExit, activityTypeSet.map((_, "void onResume()")), List("_", "a"))
  val Activity_onCreate_exit =
    I(CBExit, activityTypeSet.map((_, "void onCreate(android.os.Bundle)")), List("_", "a"))
  val Activity_onPause_entry = I(CBEnter, activityTypeSet.map((_, "void onPause()")), List("_", "a"))
  val Activity_onPause_exit = I(CBExit, activityTypeSet.map((_, "void onPause()")), List("_", "a"))
  val Activity_init_exit = I(CBExit,
    (activityTypeSet + "java.lang.Object").map((_, "void <init>()")), List("_", "a"))

  val Activity_init_entry: I = Activity_init_exit.copy(mt = CBEnter)

  // Fragment getActivity
  val Fragment_getActivity_Signatures = Set(
    ("android.app.Fragment","android.app.Activity getActivity()"),
    ("android.support.v4.app.Fragment","android.support.v4.app.FragmentActivity getActivity()"),
    ("android.support.v4.app.FragmentHostCallback","android.app.Activity getActivity()"),
    ("androidx.fragment.app.Fragment","androidx.fragment.app.FragmentActivity getActivity()")
  )
  val Fragment_get_activity_exit_null = I(CIExit, Fragment_getActivity_Signatures, "@null"::"f"::Nil)

  val Fragment_onActivityCreated_Signatures = Set(
    ("android.app.DialogFragment","void onActivityCreated(android.os.Bundle)"),
    ("android.app.Fragment","void onActivityCreated(android.os.Bundle)"),
    ("android.arch.lifecycle.ReportFragment","void onActivityCreated(android.os.Bundle)"),
    ("android.preference.PreferenceFragment","void onActivityCreated(android.os.Bundle)"),
    ("android.support.v14.preference.PreferenceFragment","void onActivityCreated(android.os.Bundle)"),
    ("android.support.v4.app.DialogFragment","void onActivityCreated(android.os.Bundle)"),
    ("android.support.v4.app.Fragment","void onActivityCreated(android.os.Bundle)"),
    ("android.support.v7.preference.PreferenceFragmentCompat","void onActivityCreated(android.os.Bundle)"),
    ("android.support.wearable.view.CardFragment","void onActivityCreated(android.os.Bundle)"),
    ("androidx.fragment.app.DialogFragment","void onActivityCreated(android.os.Bundle)"),
    ("androidx.fragment.app.Fragment","void onActivityCreated(android.os.Bundle)"),
    ("androidx.lifecycle.ReportFragment","void onActivityCreated(android.os.Bundle)"),
  )

  val Fragment_onActivityCreated_entry = I(CBEnter, Fragment_onActivityCreated_Signatures, "_"::"f"::Nil)

  val Fragment_onDestroy_Signatures = Set(
    ("android.app.Fragment","void onDestroy()"),
    ("android.app.Fragment","void onDestroyOptionsMenu()"),
    ("android.app.Fragment","void onDestroyView()"),
    ("android.arch.lifecycle.ReportFragment","void onDestroy()"),
    ("android.preference.PreferenceFragment","void onDestroy()"),
    ("android.support.v4.app.Fragment","void onDestroy()"),
    ("android.support.v4.app.FragmentActivity","void onDestroy()"),
    ("android.support.wearable.view.CardFragment","void onDestroy()"),
    ("androidx.fragment.app.DialogFragment","void onDestroyView()"),
    ("androidx.fragment.app.Fragment","void onDestroy()"),
    ("androidx.fragment.app.Fragment","void onDestroyOptionsMenu()"),
    ("androidx.fragment.app.Fragment","void onDestroyView()"),
    ("androidx.fragment.app.FragmentActivity","void onDestroy()"),
    ("androidx.fragment.app.ListFragment","void onDestroyView()"),
    ("androidx.lifecycle.ReportFragment","void onDestroy()"),
  )
  val Fragment_onDestroy_exit = I(CBExit, Fragment_onDestroy_Signatures, "_"::"f"::Nil)

  // rxjava
  val RxJava_call = Set(
    ("rx.functions.Action1","void call(java.lang.Object)"),
  )
  val RxJava_call_entry = I(CBEnter, RxJava_call, "_"::"l"::Nil)

  val RxJava_unsubscribe = Set(
    ("rx.Subscription", "void unsubscribe()"),
    ("rx.internal.operators.CachedObservable$ReplayProducer", "void unsubscribe()")
  )
  val RxJava_unsubscribe_exit = I(CIExit, RxJava_unsubscribe, "_"::"s"::Nil)

  val RxJava_subscribe = Set(
    ("rx.Single", "rx.Subscription subscribe(rx.functions.Action1)")
  )
  val RxJava_subscribe_exit = I(CIExit, RxJava_subscribe, "sr"::"s"::"l"::Nil)
  val RxJava_subscribe_exit_null = RxJava_subscribe_exit.copy(lsVars = "@null"::Nil)
}

object FragmentGetActivityNullSpec{
  val cond = Or(Not(SpecSignatures.Fragment_onActivityCreated_entry), SpecSignatures.Fragment_onDestroy_exit)
  val getActivityNull = LSSpec(cond, SpecSignatures.Fragment_get_activity_exit_null)
}

object RxJavaSpec{
  val subUnsub = NI(SpecSignatures.RxJava_subscribe_exit, SpecSignatures.RxJava_unsubscribe_exit)
  val call = LSSpec(subUnsub, SpecSignatures.RxJava_call_entry)
  val subscribeDoesNotReturnNull = LSSpec(LSFalse, SpecSignatures.RxJava_subscribe_exit_null)
}

object ActivityLifecycle {
  val resumePause = NI(SpecSignatures.Activity_onResume_entry, SpecSignatures.Activity_onPause_exit)
  val initPause = NI(SpecSignatures.Activity_onResume_entry, SpecSignatures.Activity_init_exit)
  val onPause_onlyafter_onResume_init = LSSpec(And(resumePause,initPause),
    SpecSignatures.Activity_onPause_entry)
  val init_first_callback =
    LSSpec(And(
      Not(SpecSignatures.Activity_onCreate_exit),
      And(Not(SpecSignatures.Activity_onResume_exit),
        Not(SpecSignatures.Activity_onPause_exit))
    ),
      SpecSignatures.Activity_init_entry)
  val spec = new SpecSpace(Set(onPause_onlyafter_onResume_init))
}
