package edu.colorado.plv.bounder.lifestate

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{CBEnter, CBExit}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, I, LSSpec, NI}

object SpecSignatures {
  // TODO; get all specs out of ls def
  val activityTypeSet = Set(
    "androidx.appcompat.app.AppCompatActivity",
    "androidx.fragment.app.FragmentActivity",
    "androidx.core.app.ComponentActivity",
    "android.app.Activity",
  )

  // Activity lifecycle
  val Activity_onResume_entry = I(CBEnter, activityTypeSet.map((_, "void onResume()")), List("_", "a"))
  val Activity_onResume_exit = I(CBExit, activityTypeSet.map((_, "void onResume()")), List("_", "a"))
  val Activity_onPause_entry = I(CBEnter, activityTypeSet.map((_, "void onPause()")), List("_", "a"))
  val Activity_onPause_exit = I(CBExit, activityTypeSet.map((_, "void onPause()")), List("_", "a"))
  val Activity_init_exit = I(CBExit,
    (activityTypeSet + "java.lang.Object").map((_, "void <init>()")), List("_", "a"))

  // Fragment getActivity
  val Fragment_getActivity_Signatures = Set(
    ("android.app.Fragment","android.app.Activity getActivity()"),
    ("android.support.v4.app.Fragment","android.support.v4.app.FragmentActivity getActivity()"),
    ("android.support.v4.app.FragmentHostCallback","android.app.Activity getActivity()")
  )
  val Fragment_get_activity_exit_null = I(CBExit, Fragment_getActivity_Signatures, "@null"::"f"::Nil)

  val Fragment_onActivityCreated_Signatures = Set(
    ("android.app.Fragment","void onActivityCreated(android.os.Bundle)"),
    ("android.support.v4.app.Fragment","void onActivityCreated(android.os.Bundle)"),
    ("android.support.v4.app.DialogFragment","void onActivityCreated(android.os.Bundle)"),
    ("android.app.DialogFragment","void onActivityCreated(android.os.Bundle)"),
    ("android.arch.lifecycle.ReportFragment","void onActivityCreated(android.os.Bundle)"),
    ("android.preference.PreferenceFragment","void onActivityCreated(android.os.Bundle)"),
    ("android.support.v14.preference.PreferenceFragment","void onActivityCreated(android.os.Bundle)"),
    ("android.support.v7.preference.PreferenceFragmentCompat","void onActivityCreated(android.os.Bundle)"),
    ("android.support.wearable.view.CardFragment","void onActivityCreated(android.os.Bundle)"),
  )

  val Fragment_onActivityCreated_entry = I(CBEnter, Fragment_onActivityCreated_Signatures, "_"::"f"::Nil)

  val Fragment_onDestroy_Signatures = Set(
    ("android.app.Fragment","void onDestroyView()"),
    ("android.app.Fragment","void onDestroy()"),
    ("android.app.Fragment","void onDestroyOptionsMenu()"),
    ("android.support.v4.app.Fragment","void onDestroy()"),
    ("android.support.v4.app.Fragment","void onDestroyOptionsMenu()"),
    ("android.support.v4.app.Fragment","void onDestroyView()"),
    ("android.support.v4.app.FragmentActivity","void onDestroy()"),
    ("android.support.v4.app.DialogFragment","void onDestroyView()"),
    ("android.app.DialogFragment","void onDestroyView()"),
    ("android.arch.lifecycle.ReportFragment","void onDestroy()"),
    ("android.preference.PreferenceFragment","void onDestroyView()"),
    ("android.preference.PreferenceFragment","void onDestroy()"),
    ("android.support.v14.preference.PreferenceFragment","void onDestroyView()"),
    ("android.support.v4.app.ListFragment","void onDestroyView()"),
    ("android.support.v7.preference.PreferenceFragmentCompat","void onDestroyView()"),
    ("android.support.wearable.view.CardFragment","void onDestroy()"),
  )
  val Fragment_onDestroy_exit = I(CBExit, Fragment_onDestroy_Signatures, "_"::"f"::Nil)
}

object ResumePauseSpec {
  val resumePause = NI(SpecSignatures.Activity_onResume_entry, SpecSignatures.Activity_onPause_exit)
  val initPause = NI(SpecSignatures.Activity_onResume_entry, SpecSignatures.Activity_init_exit)
  val testSpec1 = LSSpec(And(resumePause,initPause),
    SpecSignatures.Activity_onPause_entry)
  val spec = new SpecSpace(Set(testSpec1))
}
