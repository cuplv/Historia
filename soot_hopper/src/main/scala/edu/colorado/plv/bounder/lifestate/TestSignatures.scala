package edu.colorado.plv.bounder.lifestate

import edu.colorado.plv.bounder.ir.{CBEnter, CBExit}
import edu.colorado.plv.bounder.lifestate.LifeState.I

object TestSignatures {
  val Activity_onResume_entry = I(CBEnter, Set(("android.app.Activity", "void onResume()")), List("_", "a"))
  val Activity_onResume_exit = I(CBExit, Set(("android.app.Activity", "void onResume()")), List("_", "a"))
  val Activity_onPause_entry = I(CBEnter, Set(("android.app.Activity", "void onPause()")), List("_", "a"))
  val Activity_onPause_exit = I(CBExit, Set(("android.app.Activity", "void onPause()")), List("_", "a"))
  val Activity_init_exit = I(CBExit, Set(("android.app.Activity", "void <init>()")), List("_", "a"))

}
