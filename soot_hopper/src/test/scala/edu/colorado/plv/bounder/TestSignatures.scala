package edu.colorado.plv.bounder

import edu.colorado.plv.bounder.ir.{CBEnter, CBExit}
import edu.colorado.plv.bounder.lifestate.LifeState.I

object TestSignatures {
  val Activity_onResume_entry = I(CBEnter, Set(("android.app.Activity", "onResume")), List("_", "a"))
  val Activity_onPause_entry = I(CBEnter, Set(("android.app.Activity", "onPause")), List("_", "a"))
  val Activity_onPause_exit = I(CBExit, Set(("android.app.Activity", "onPause")), List("_", "a"))
}
