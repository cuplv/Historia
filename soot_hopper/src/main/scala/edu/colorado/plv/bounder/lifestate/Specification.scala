package edu.colorado.plv.bounder.lifestate

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{CBEnter, CBExit, CIEnter, CIExit}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, I, LSConstraint, LSFalse, LSPred, LSSpec, LSTrue, NI, Not, Or, SetSignatureMatcher, SignatureMatcher, SubClassMatcher}
import edu.colorado.plv.bounder.symbolicexecutor.state.{Equals, NotEquals}

object SpecSignatures {

  //SetSignatureMatcher(activityTypeSet.map((_, "void onCreate(android.os.Bundle)")))

  // Activity lifecycle
  val Activity = Set("android.app.Activity", "androidx.fragment.app.FragmentActivity")

  val Activity_onResume: SignatureMatcher =
    SubClassMatcher(Activity, "void onResume\\(\\)", "Activity_onResume")
  val Activity_onCreate: SignatureMatcher =
    SubClassMatcher(Activity, "void onCreate\\(android.os.Bundle\\)",
    "Activity_onCreate")
  val Activity_finish: SignatureMatcher =
    SubClassMatcher(Activity, "void finish\\(\\)", "Activity_finish")
  val Activity_onResume_entry: I =
    I(CBEnter, Activity_onResume, List("_", "a"))
  val Activity_onResume_exit: I =
    I(CBExit, Activity_onResume, List("_", "a"))
  val Activity_onCreate_exit: I =
    I(CBExit, Activity_onCreate, List("_", "a"))

  val Activity_onCreate_entry: I =
    I(CBEnter, Activity_onCreate, List("_", "a"))

  val Activity_onPause: SignatureMatcher =
    SubClassMatcher(Activity,"void onPause\\(\\)", "Activity_onPause")
  val Activity_onPause_entry: I = I(CBEnter, Activity_onPause, List("_", "a"))
  val Activity_onPause_exit: I =
    I(CBExit, Activity_onPause, List("_", "a"))
  val Activity_init: SignatureMatcher =
    SubClassMatcher(Activity, "void \\<init\\>.*", "Activity_init")
  val Activity_init_exit: I =
    I(CBExit,Activity_init, List("_", "a"))
  val Activity_onDestroy: SignatureMatcher =
    SubClassMatcher(Activity, "void onDestroy\\(\\)", "Activity_onDestroy")
  val Activity_onDestroy_exit: I = I(CBExit, Activity_onDestroy, List("_","a"))

  val Activity_init_entry: I = Activity_init_exit.copy(mt = CBEnter)

  val Activity_findView: SignatureMatcher=
    SubClassMatcher(Activity,".*findViewById.*","Activity_findView")
  val Activity_findView_exit: I = I(CIExit,
    Activity_findView, List("v","a"))

  // Fragment getActivity
  private val Fragment = Set("android.app.Fragment","androidx.fragment.app.Fragment","android.support.v4.app.Fragment")
  val Fragment_getActivity: SignatureMatcher= SubClassMatcher(Fragment,
  ".*Activity getActivity\\(\\)", "Fragment_getActivity")
  val Fragment_get_activity_exit_null: I = I(CIExit, Fragment_getActivity, "@null"::"f"::Nil)

  val Fragment_get_activity_exit: I = I(CIExit, Fragment_getActivity, "a"::"f"::Nil)

  val Fragment_onActivityCreated: SignatureMatcher = SubClassMatcher(Fragment,
  "void onActivityCreated\\(android.os.Bundle\\)", "Fragment_onActivityCreated")

  val Fragment_onActivityCreated_entry: I = I(CBEnter, Fragment_onActivityCreated, "_"::"f"::Nil)

  val Fragment_onDestroy_Signatures: SignatureMatcher = SubClassMatcher(Fragment, "void onDestroy\\(\\)", "Fragment_onDestroy")
  val Fragment_onDestroy_exit: I = I(CBExit, Fragment_onDestroy_Signatures, "_"::"f"::Nil)

  // rxjava
  val RxJava_call: SignatureMatcher = SubClassMatcher("rx.functions.Action1", "void call\\(java.lang.Object\\)", "rxJava_call")

  val RxJava_call_entry: I = I(CBEnter, RxJava_call, "_"::"l"::Nil)

  val Subscriber = Set("rx.Subscriber","rx.SingleSubscriber","rx.Subscription",
    "rx.subscriptions.RefCountSubscription",
    "rx.subscriptions.RefCountSubscription")
  val RxJava_unsubscribe: SignatureMatcher = SubClassMatcher(Subscriber, "void unsubscribe\\(\\)", "rxJava_unsubscribe")

  val RxJava_unsubscribe_exit: I = I(CIExit, RxJava_unsubscribe, "_"::"s"::Nil)

  val RxJava_subscribe: SignatureMatcher =
    SubClassMatcher("rx.Single", "rx.Subscription subscribe\\(rx.functions.Action1\\)",
      "RxJava_subscribe")
  val RxJava_subscribe_exit: I = I(CIExit, RxJava_subscribe, "s"::"_"::"l"::Nil)
  val RxJava_subscribe_exit_null: I = RxJava_subscribe_exit.copy(lsVars = "@null"::Nil)
}

object FragmentGetActivityNullSpec{
//  val cond = Or(Not(SpecSignatures.Fragment_onActivityCreated_entry), SpecSignatures.Fragment_onDestroy_exit)
  val cond: LSPred = NI(SpecSignatures.Fragment_onDestroy_exit, SpecSignatures.Fragment_onActivityCreated_entry)
  val getActivityNull: LSSpec = LSSpec(cond, SpecSignatures.Fragment_get_activity_exit_null)
  val getActivityNonNull: LSSpec = LSSpec(Not(cond), SpecSignatures.Fragment_get_activity_exit,
    Set(LSConstraint("a", NotEquals, "@null")))
}

object RxJavaSpec{
  val subUnsub:LSPred = NI(
    SpecSignatures.RxJava_subscribe_exit,
    SpecSignatures.RxJava_unsubscribe_exit)
  val call:LSSpec = LSSpec(subUnsub, SpecSignatures.RxJava_call_entry)
//  val subscribeDoesNotReturnNull = LSSpec(LSFalse, SpecSignatures.RxJava_subscribe_exit_null)
  private val subscribe_s_only = SpecSignatures.RxJava_subscribe_exit.copy(lsVars = "s"::Nil)
  val subscribeIsUnique:LSSpec = LSSpec(Not(subscribe_s_only),
    subscribe_s_only) //,Set(LSConstraint("s",NotEquals,"@null")  )
  val spec = Set(call,subscribeIsUnique)
}

object LifecycleSpec {
  //TODO:===== destroyed
  val viewAttached: LSPred = SpecSignatures.Activity_findView_exit //TODO: ... or findView on other view
  val destroyed: LSPred = NI(SpecSignatures.Activity_onDestroy_exit, SpecSignatures.Activity_onCreate_entry)
  val created: LSPred = NI(SpecSignatures.Activity_onCreate_entry, SpecSignatures.Activity_onDestroy_exit)
  val resumed: LSPred =
    NI(SpecSignatures.Activity_onResume_entry, SpecSignatures.Activity_onPause_exit)
//  val initPause = NI(SpecSignatures.Activity_onResume_entry, SpecSignatures.Activity_init_exit)
  val Activity_onResume_onlyafter_onPause: LSSpec = LSSpec(NI(SpecSignatures.Activity_onPause_exit,
    SpecSignatures.Activity_onResume_entry), SpecSignatures.Activity_onResume_entry)
  val Activity_onPause_onlyafter_onResume_init: LSSpec = LSSpec(And(resumed,SpecSignatures.Activity_init_exit),
    SpecSignatures.Activity_onPause_entry)
  val init_first_callback: LSSpec =
    LSSpec(
      And(Not(SpecSignatures.Activity_onCreate_exit),
      And(Not(SpecSignatures.Activity_onResume_exit),
        Not(SpecSignatures.Activity_onPause_exit))
    ),
      SpecSignatures.Activity_init_entry)
  val Activity_created:LSPred = NI(SpecSignatures.Activity_onCreate_entry, SpecSignatures.Activity_onDestroy_exit)
  val Fragment_activityCreatedOnlyFirst:LSSpec = LSSpec(
    And(
      Not(SpecSignatures.Fragment_onDestroy_exit),
      And(Not(SpecSignatures.Fragment_onActivityCreated_entry),
      Not(SpecSignatures.Fragment_onActivityCreated_entry))
    ),
    SpecSignatures.Fragment_onActivityCreated_entry)

  val Activity_createdOnlyFirst:LSSpec = LSSpec(
    Not(SpecSignatures.Activity_onCreate_entry), SpecSignatures.Activity_onCreate_entry
  )

  val spec:Set[LSSpec] = Set(Fragment_activityCreatedOnlyFirst,
    Activity_createdOnlyFirst,
    Activity_onPause_onlyafter_onResume_init,
    init_first_callback)
}

object ViewSpec {
  val anyViewCallin: I = I(CIEnter, SubClassMatcher("android.view.View",".*","View_AnyExceptOther"),List("_", "v") )
  val onClick:SignatureMatcher = SubClassMatcher("android.view.View$OnClickListener", ".*onClick.*", "ViewOnClickListener_onClick")
  val setOnClickListener:LSPred = I(CIExit,
    SubClassMatcher("android.view.View",".*setOnClickListener.*","View_setOnClickListener"),
    List("_","v","l")
  )

  val disallowCallinAfterActivityPause:LSSpec = LSSpec(And(LifecycleSpec.viewAttached,
    LifecycleSpec.destroyed),
    anyViewCallin)

  //TODO: uncomment=================
//  val clickWhileActive:LSSpec = LSSpec(And(setOnClickListener,And(LifecycleSpec.viewAttached,
//    LifecycleSpec.created)),
//    I(CBEnter, onClick, List("_", "l")))
  val clickWhileActive:LSSpec = LSSpec(
    And(And(setOnClickListener, LifecycleSpec.viewAttached), Or(LifecycleSpec.resumed,
      I(CIExit, SpecSignatures.Activity_finish, "_"::"a"::Nil))),
    I(CBEnter, onClick, List("_", "l")))
}

//TODO: multiple signature matchers matching the same method is not supported
//object ObjectSpec {
//  val anyCb:I = I(CBEnter, SubClassMatcher("java.lang.Object", ".*", "anyMethod"), List("_"))
//  val clinitExit:I = I(CBEnter, SubClassMatcher("java.lang.Object", ".*\\<clinit\\>.*", "clinit"), List())
//  val clinitFirst:LSSpec = LSSpec(Not(anyCb),clinitExit)
//}