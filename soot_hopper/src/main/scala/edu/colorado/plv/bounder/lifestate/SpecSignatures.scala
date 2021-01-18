package edu.colorado.plv.bounder.lifestate

import edu.colorado.plv.bounder.ir.{CBEnter, CBExit}
import edu.colorado.plv.bounder.lifestate.LifeState.I

object SpecSignatures {
  // TODO; get all specs out of ls def
  val activityTypeSet = Set(
    "androidx.appcompat.app.AppCompatActivity",
    "androidx.fragment.app.FragmentActivity",
    "androidx.core.app.ComponentActivity",
    "android.app.Activity",
  )
  val Activity_onResume_entry = I(CBEnter, activityTypeSet.map((_, "void onResume()")), List("_", "a"))
  val Activity_onResume_exit = I(CBExit, activityTypeSet.map((_, "void onResume()")), List("_", "a"))
  val Activity_onPause_entry = I(CBEnter, activityTypeSet.map((_, "void onPause()")), List("_", "a"))
  val Activity_onPause_exit = I(CBExit, activityTypeSet.map((_, "void onPause()")), List("_", "a"))
  val Activity_init_exit = I(CBExit,activityTypeSet.map((_, "void <init>()")), List("_", "a"))

}
