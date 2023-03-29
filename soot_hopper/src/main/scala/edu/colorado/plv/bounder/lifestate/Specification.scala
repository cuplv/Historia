package edu.colorado.plv.bounder.lifestate

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{CBEnter, CBExit, CIEnter, CIExit}
import edu.colorado.plv.bounder.lifestate.LifeState.{AbsMsg, And, Forall, HNOE, LSConstraint, LSFalse, LSPred, LSSpec, LSTrue, NS, Not, OAbsMsg, Or, SetSignatureMatcher, SignatureMatcher, SubClassMatcher}
import edu.colorado.plv.bounder.lifestate.SpecSignatures.{Fragment_onStart_entry, Fragment_onStop_exit, t}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BoolVal, Equals, NamedPureVar, NotEquals, NullVal, PureExpr, TopVal}

object SpecSignatures {
  val a = NamedPureVar("a")
  val s = NamedPureVar("s")
  val f = NamedPureVar("f")
  val l = NamedPureVar("l")
  val t = NamedPureVar("t")
  val v = NamedPureVar("v")
  implicit val convertList:List[String]=>List[PureExpr] = LSExpParser.convertList
//  implicit val convert:String=>PureExpr = LSExpParser.convert


  //SetSignatureMatcher(activityTypeSet.map((_, "void onCreate(android.os.Bundle)")))

  // Activity lifecycle
  val Activity = Set("android.app.Activity", "androidx.fragment.app.FragmentActivity")
  val Button = Set("android.widget.Button")

  val Activity_onResume: SignatureMatcher =
    SubClassMatcher(Activity, "void onResume\\(\\)", "Activity_onResume")
  val Activity_onCreate: SignatureMatcher =
    SubClassMatcher(Activity, "void onCreate\\(android.os.Bundle\\)",
    "Activity_onCreate")
  val Activity_finish: SignatureMatcher =
    SubClassMatcher(Activity, "void finish\\(\\)", "Activity_finish")
  val Activity_onResume_entry: OAbsMsg =
    AbsMsg(CBEnter, Activity_onResume, List(TopVal, a))
  val Activity_onResume_exit: OAbsMsg =
    AbsMsg(CBExit, Activity_onResume, List(TopVal, a))
  val Activity_onCreate_exit: OAbsMsg =
    AbsMsg(CBExit, Activity_onCreate, List(TopVal, a))

  val Activity_onCreate_entry: OAbsMsg =
    AbsMsg(CBEnter, Activity_onCreate, List(TopVal, a))

  val Activity_onPause: SignatureMatcher =
    SubClassMatcher(Activity,"void onPause\\(\\)", "Activity_onPause")
  val Activity_onPause_entry: OAbsMsg = AbsMsg(CBEnter, Activity_onPause, List(TopVal, a))
  val Activity_onPause_exit: OAbsMsg =
    AbsMsg(CBExit, Activity_onPause, List(TopVal, a))
//  val Activity_init: SignatureMatcher =
//    SubClassMatcher(Activity, "void \\<init\\>.*", "Activity_init")
//  val Activity_init_exit: I =
//    I(CBExit,Activity_init, List("_", "a"))
  val Activity_onDestroy: SignatureMatcher =
    SubClassMatcher(Activity, "void onDestroy\\(\\)", "Activity_onDestroy")
  val Activity_onDestroy_exit: OAbsMsg = AbsMsg(CBExit, Activity_onDestroy, List(TopVal,a))

//  val Activity_init_entry: I = Activity_init_exit.copy(mt = CBEnter)

  val Activity_findView: SignatureMatcher=
    SubClassMatcher(Activity,".*findViewById.*","Activity_findView")
  val Activity_findView_exit: OAbsMsg = AbsMsg(CIExit,
    Activity_findView, List(v,a))

  val Activity_getLayoutInflater: OAbsMsg =
    AbsMsg(CIExit, SubClassMatcher(Activity,".*getLayoutInflater.*","getLayoutInflater"), NullVal::a::Nil)
//  // 1min 09 sec
  // note: this kind of specification can go in "NonNullReturnCallins.txt"
//  val Activity_getLayoutInflater_nonNull = LSSpec(a::Nil, Nil, LSFalse, Activity_getLayoutInflater)

  val Button_init: OAbsMsg = AbsMsg(CIExit, SubClassMatcher(Button, ".*<init>.*", "Button_init"), List(TopVal, v))

  // Fragment getActivity
  val Fragment = Set("android.app.Fragment","androidx.fragment.app.Fragment","android.support.v4.app.Fragment")

  val Fragment_onStart_entry = AbsMsg(CBEnter,
    SubClassMatcher(Fragment, "void onStart\\(\\)", "Fragment_onStart_entry"), TopVal::f::Nil)
  val Fragment_onStop_exit = AbsMsg(CBExit,
    SubClassMatcher(Fragment, "void onStop\\(\\)", "Fragment_onStop_exit"), TopVal::f::Nil
  )
  val Fragment_getActivity: SignatureMatcher= SubClassMatcher(Fragment,
  ".*Activity getActivity\\(\\)", "Fragment_getActivity")
  val Fragment_get_activity_exit_null: OAbsMsg = AbsMsg(CIExit, Fragment_getActivity, NullVal::f::Nil)

  val Fragment_get_activity_exit: OAbsMsg = AbsMsg(CIExit, Fragment_getActivity, a::f::Nil)

  val Fragment_onActivityCreated: SignatureMatcher = SubClassMatcher(Fragment,
  "void onActivityCreated\\(android.os.Bundle\\)", "Fragment_onActivityCreated")

  val Fragment_onActivityCreated_entry: OAbsMsg = AbsMsg(CBEnter, Fragment_onActivityCreated, TopVal::f::Nil)

  val Fragment_onDestroy: SignatureMatcher = SubClassMatcher(Fragment, "void onDestroy\\(\\)", "Fragment_onDestroy")
  val Fragment_onDestroy_exit: OAbsMsg = AbsMsg(CBExit, Fragment_onDestroy, TopVal::f::Nil)

  // rxjava
  val RxJava_call: SignatureMatcher = SubClassMatcher("rx.functions.Action1", "void call\\(java.lang.Object\\)", "rxJava_call")

  val RxJava_call_entry: OAbsMsg = AbsMsg(CBEnter, RxJava_call, TopVal::l::Nil)


  //TODO: check that this actually matches things
  val RxJava_create: SignatureMatcher = SubClassMatcher("rx.Single", "rx.Single create\\(rx.Single#OnSubscribe\\)", "rxJava_create")
  val RxJava_create_exit:OAbsMsg = AbsMsg(CIExit, RxJava_create, t::Nil)

  val Subscriber = Set("rx.Subscriber","rx.SingleSubscriber","rx.Subscription",
    "rx.subscriptions.RefCountSubscription",
    "rx.subscriptions.RefCountSubscription")
  val RxJava_unsubscribe: SignatureMatcher = SubClassMatcher(Subscriber, "void unsubscribe\\(\\)", "rxJava_unsubscribe")

  val RxJava_unsubscribe_exit: OAbsMsg = AbsMsg(CIExit, RxJava_unsubscribe, TopVal::s::Nil)

  val RxJava_subscribe: SignatureMatcher =
    SubClassMatcher("rx.Single", "rx.Subscription subscribe\\(rx.functions.Action1\\)",
      "RxJava_subscribe")
  val RxJava_subscribe_exit: OAbsMsg = AbsMsg(CIExit, RxJava_subscribe, s::TopVal::l::Nil)
  val RxJava_subscribe_exit_null: OAbsMsg = RxJava_subscribe_exit.copyMsg(lsVars = NullVal::Nil)
}

object FragmentGetActivityNullSpec{

  val a = NamedPureVar("a")
  val f = NamedPureVar("f")
//  val cond = Or(Not(SpecSignatures.Fragment_onActivityCreated_entry), SpecSignatures.Fragment_onDestroy_exit)
  val fragmentActivityNotAttached: LSPred =
    Or(NS(SpecSignatures.Fragment_onDestroy_exit, SpecSignatures.Fragment_onActivityCreated_entry),
      Not(SpecSignatures.Fragment_onActivityCreated_entry))
  val fragmentActivityAttached: LSPred =
    NS(SpecSignatures.Fragment_onActivityCreated_entry,SpecSignatures.Fragment_onDestroy_exit)
  val getActivityNull: LSSpec = LSSpec(a::f::Nil, Nil,
    fragmentActivityNotAttached, SpecSignatures.Fragment_get_activity_exit,
    Set(LSConstraint(a, Equals, NullVal)))
//  val getActivityNonNull: LSSpec = LSSpec("a"::"f"::Nil, Nil,
//    fragmentActivityAttached, SpecSignatures.Fragment_get_activity_exit,
//    Set(LSConstraint("a", NotEquals, "@null")))
  val getActivityNonNull:LSSpec = LSSpec(a::f::Nil, Nil, LSTrue, SpecSignatures.Fragment_get_activity_exit)
}

object RxJavaSpec{
  import SpecSignatures.v

  val l = NamedPureVar("l")
  val m = NamedPureVar("m")
  val s = NamedPureVar("s")
  //TODO: \/ I(create(l)) =======
  val subUnsub:LSPred = NS(
    SpecSignatures.RxJava_subscribe_exit,
    SpecSignatures.RxJava_unsubscribe_exit)
  val call:LSSpec = LSSpec(l::Nil, s::Nil, subUnsub, SpecSignatures.RxJava_call_entry)
//  val subscribeDoesNotReturnNull = LSSpec(LSFalse, SpecSignatures.RxJava_subscribe_exit_null)
  val subscribe_s_only = SpecSignatures.RxJava_subscribe_exit.copyMsg(lsVars = s::Nil)
  val subscribeIsUnique:LSSpec = LSSpec(s::Nil, Nil, Not(subscribe_s_only),
    subscribe_s_only) //,Set(LSConstraint("s",NotEquals,"@null")  )
  val subscribeNonNull = LSSpec(Nil,Nil, LSFalse, SpecSignatures.RxJava_subscribe_exit.copyMsg(lsVars = NullVal::Nil))
  val spec = Set(call,subscribeIsUnique)
  val subscribeCB = AbsMsg(CBEnter,
    SubClassMatcher("io.reactivex.MaybeOnSubscribe","void subscribe\\(io.reactivex.MaybeEmitter\\)", "subscribeCB"),
    TopVal::l::Nil
  )
  val Maybe = Set("io.reactivex.Maybe")
  val Maybe_create = AbsMsg(CIExit,SubClassMatcher(Maybe,
    "io.reactivex.Maybe create\\(io.reactivex.MaybeOnSubscribe\\)", "Maybe_create"), m::TopVal::l::Nil )
  val Disposable = Set("io.reactivex.disposables.Disposable")
  val Disposable_dispose = AbsMsg(CIExit, SubClassMatcher(Disposable,"void dispose\\(\\)","Disposable_dispose"),
    TopVal::s::Nil)
  val Maybe_create_unique = LSSpec(m::Nil, Nil, Not(Maybe_create.copy(lsVars = m::Nil)),
    Maybe_create.copy(lsVars = m::Nil))

  def retSame(signature:String, ident:String):LSSpec =
     LSSpec(v::t::Nil, Nil,LSConstraint(t,Equals,v),
       AbsMsg(CIExit, SubClassMatcher(Maybe, signature, ident), t::v::Nil))
  val Maybe_subscribeOn = retSame("io.reactivex.Maybe subscribeOn\\(io.reactivex.Scheduler\\)",
    "Maybe_subscribeOn")
  val Maybe_observeOn = retSame("io.reactivex.Maybe observeOn\\(io.reactivex.Scheduler\\)",
    "Maybe_observeOn")
  val Maybe_subscribeCi = AbsMsg(CIExit,
    SubClassMatcher(Maybe,
      "io.reactivex.disposables.Disposable " +
        "subscribe\\(io.reactivex.functions.Consumer,io.reactivex.functions.Consumer\\)",
      "Maybe_subscribeCI"), s::m::Nil)
  val subscribeSpec = LSSpec(l :: Nil, m :: s :: Nil,
    And(Maybe_create, NS(Maybe_subscribeCi, Disposable_dispose)), subscribeCB)


}

object LifecycleSpec {
  val a = NamedPureVar("a")
  val f = NamedPureVar("f")
  val v = NamedPureVar("v")
  //TODO: ======= check if this fixes connectBot
  val noResumeWhileFinish: LSSpec = LSSpec(a::Nil, Nil,
    Not(AbsMsg(CIExit, SpecSignatures.Activity_finish, TopVal::a::Nil)),
    SpecSignatures.Activity_onResume_entry
  )
  val startStopAlternation:LSSpec = LSSpec(f::Nil, Nil, Or(
    And(Not(SpecSignatures.Fragment_onStart_entry), Not(SpecSignatures.Fragment_onStop_exit.copy(mt = CBEnter))),
    NS(SpecSignatures.Fragment_onStop_exit.copy(mt=CBEnter), SpecSignatures.Fragment_onStart_entry)
  ),SpecSignatures.Fragment_onStart_entry)
  val stopStartAlternation:LSSpec = LSSpec(f::Nil, Nil,
    NS(Fragment_onStart_entry, Fragment_onStop_exit.copy(mt = CBEnter)),
    SpecSignatures.Fragment_onStop_exit.copy(mt = CBEnter))

  val viewAttached: LSPred = SpecSignatures.Activity_findView_exit //TODO: ... or findView on other view
  val destroyed: LSPred = NS(SpecSignatures.Activity_onDestroy_exit, SpecSignatures.Activity_onCreate_entry)
  val created: LSPred = NS(SpecSignatures.Activity_onCreate_entry, SpecSignatures.Activity_onDestroy_exit)
  val resumed: LSPred =
    NS(SpecSignatures.Activity_onResume_entry, SpecSignatures.Activity_onPause_exit)
  val paused:LSPred =
    Or(Not(SpecSignatures.Activity_onResume_entry),
      NS(SpecSignatures.Activity_onPause_exit, SpecSignatures.Activity_onResume_entry))
  val Activity_onResume_first_orAfter_onPause: LSSpec = LSSpec(a::Nil, Nil, Or(
    NS(SpecSignatures.Activity_onPause_exit, SpecSignatures.Activity_onResume_entry),
    And(Not(SpecSignatures.Activity_onPause_exit),Not(SpecSignatures.Activity_onResume_entry)))
    , SpecSignatures.Activity_onResume_entry)
  //val Activity_onResume_dummy:LSSpec = LSSpec("a"::Nil, Nil, LSTrue, SpecSignatures.Activity_onResume_entry)
  val Activity_onPause_onlyafter_onResume: LSSpec = LSSpec(a::Nil, Nil, resumed,
    SpecSignatures.Activity_onPause_entry)
  val Activity_created:LSPred = NS(SpecSignatures.Activity_onCreate_entry, SpecSignatures.Activity_onDestroy_exit)
  val Fragment_activityCreatedOnlyFirst:LSSpec = LSSpec(f::Nil, Nil,
    And(
      Not(SpecSignatures.Fragment_onDestroy_exit),
      And(Not(SpecSignatures.Fragment_onActivityCreated_entry),
      Not(SpecSignatures.Fragment_onActivityCreated_entry))
    ),
    SpecSignatures.Fragment_onActivityCreated_entry)
  val Fragment_activityCreatedOnlyOnce:LSSpec = LSSpec(f::Nil, Nil,
      Not(SpecSignatures.Fragment_onActivityCreated_entry),
    SpecSignatures.Fragment_onActivityCreated_entry)

//  val Activity_createdOnlyFirst:LSSpec = LSSpec("a"::Nil, Nil,
//    And(Not(SpecSignatures.Activity_onCreate_entry),Not(SpecSignatures.Activity_onDestroy_exit)),
//    SpecSignatures.Activity_onCreate_entry
//  )
  val Activity_createdOnlyFirst:LSSpec = LSSpec(a::Nil, Nil, Not(SpecSignatures.Activity_onCreate_entry),
    SpecSignatures.Activity_onCreate_entry)
//  val Activity_destroyAfterCreate:LSSpec = LSSpec("a"::Nil, Nil,
//    NI(SpecSignatures.Activity_onCreate_entry, SpecSignatures.Activity_onDestroy_exit),
//    SpecSignatures.Activity_onDestroy_exit)

  // TODO: This seems to cause timeouts when combined with the onClick spec
  val spec:Set[LSSpec] = Set(
    Fragment_activityCreatedOnlyFirst,
    Activity_createdOnlyFirst,
//    Activity_destroyAfterCreate, // Note: tried adding this because of a failing test, did not help
    Activity_onPause_onlyafter_onResume
  )
//    init_first_callback)
}

object ViewSpec {
  val a = NamedPureVar("a")
  val b = NamedPureVar("b")
  val b2 = NamedPureVar("b2")
  val a2 = NamedPureVar("a2")
  val v = NamedPureVar("v")
  val v2 = NamedPureVar("v2")
  val l = NamedPureVar("l")

  implicit val convertList:List[String]=>List[PureExpr] = LSExpParser.convertList

  val anyViewCallin: OAbsMsg = AbsMsg(CIEnter, SubClassMatcher("android.view.View",".*","View_AnyExceptOther"),List(TopVal, v) )
  val onClick:SignatureMatcher = SubClassMatcher("android.view.View$OnClickListener", ".*onClick.*", "ViewOnClickListener_onClick")
  val menuItemOnClick:SignatureMatcher = SubClassMatcher("android.view.MenuItem$OnMenuItemClickListener",
    ".*onMenuItemClick.*","OnMenuItemClickListener_onMenuItemClick")
  val onClickI = AbsMsg(CBEnter, onClick, List(TopVal,l,v))
  val onMenuItemClickI = AbsMsg(CBEnter, menuItemOnClick, List(TopVal,l,v))
  val setOnClickListenerI:OAbsMsg = AbsMsg(CIExit,
    SubClassMatcher("android.view.View",".*setOnClickListener.*","View_setOnClickListener"),
    List(TopVal,v,l)
  )
  val setOnClickListenerIl2:AbsMsg = AbsMsg(CIExit,
    SubClassMatcher("android.view.View",".*setOnClickListener.*","View_setOnClickListener"),
    List(TopVal,v,TopVal)
  )
  val setOnClickListenerINull = AbsMsg(CIExit,
    SubClassMatcher("android.view.View",".*setOnClickListener.*","View_setOnClickListener"),
    List(TopVal,v,NullVal)
  )

   val setOnClickListener:LSPred = NS(setOnClickListenerI, setOnClickListenerINull) // TODO: setOnClickListenerIl2 causes bad proof in "finish allows click after pause, why?
//  val setOnClickListener:LSPred = setOnClickListenerI

  //TODO: fix disallowCallinAfterActivityPause , .* doesn't work as a matcher due to overlap
  // v a - viewAttached
  // a - destroyed
  val disallowCallinAfterActivityPause:LSSpec = LSSpec(v::Nil, a::Nil, And(LifecycleSpec.viewAttached,
    LifecycleSpec.destroyed),
    anyViewCallin)

  //TODO: simpler spec may be possible for click
//  val clickWhileActive:LSSpec = LSSpec(l::Nil, v::Nil, setOnClickListener,AbsMsg(CBEnter,onClick, List(TopVal, l)))
  val clickWhileActive:LSSpec = LSSpec(l::Nil,a::v::Nil,
    And(And(setOnClickListener, LifecycleSpec.viewAttached), Or(LifecycleSpec.resumed,
      AbsMsg(CIExit, SpecSignatures.Activity_finish, TopVal::a::Nil))),
    AbsMsg(CBEnter, onClick, List(TopVal, l)))

  val setEnabled:SubClassMatcher = SubClassMatcher(Set("android.view.View"), ".*setEnabled.*", "View_setEnabled")
  val buttonEnabled = Or(Not(AbsMsg(CIExit, setEnabled, TopVal::v::BoolVal(false)::Nil)),
    NS(AbsMsg(CIExit, setEnabled, TopVal::v::BoolVal(true)::Nil), AbsMsg(CIExit, setEnabled, TopVal::v::BoolVal(false)::Nil))
  )
//  private val buttonEnabled = Not(I(CIExit, setEnabled, "_"::"v"::"@false"::Nil)) //testing version, delete later
  val clickWhileNotDisabled:LSSpec = LSSpec(l::Nil, v::Nil,
    And(setOnClickListenerI, buttonEnabled),
    AbsMsg(CBEnter, onClick, List(TopVal, l)))
  val fv1 = AbsMsg(CIExit, SpecSignatures.Activity_findView, v::a::Nil)
  val fv2 = AbsMsg(CIExit, SpecSignatures.Activity_findView, v::a2::Nil)
  val fv_exit = AbsMsg(CIExit, SpecSignatures.Activity_findView, v::TopVal::Nil)
  // ¬ I(ci v:=a2.findViewByID()) /\ a != a2 ]
  // Ɐv,a,a2. ¬ I(ci v:= a2.findViewByID()) \/ a = a2 <= ci v:= a.findViewByID()
  val viewOnlyReturnedFromOneActivity_pre_HNOE:LSSpec =
    LSSpec(a::v::Nil, Nil, Forall(a2::Nil, Or(Not(fv2), LSConstraint(a, Equals, a2))), fv1)
  val viewOnlyReturnedFromOneActivity:LSSpec =
    LSSpec(a::v::Nil, Nil, HNOE(a2,fv2,a), fv1)
//  val sameIDSameView:LSSpec =
//    LSSpec()

//  val noDupeFindView:LSSpec = LSSpec("v"::Nil,Nil, Not(fv_exit), fv_exit)  //TODO: UNSOUND test version of noDupe
}
object SAsyncTask{
  val t = NamedPureVar("t")
  val v = NamedPureVar("v")
  val AsyncTaskC = Set("android.os.AsyncTask")
  val executeSig = SubClassMatcher(AsyncTaskC, ".*AsyncTask execute\\(.*\\)", "AsyncTask_execute")
  val executeI = AbsMsg(CIExit, executeSig, TopVal::t::Nil)
  val executeIEntry =
    AbsMsg(CIEnter, executeSig, TopVal::t::Nil)
  val disallowDoubleExecute:LSSpec = LSSpec(t::Nil, Nil, executeI, executeIEntry )
  val postExecute = SubClassMatcher(AsyncTaskC, ".*onPostExecute\\(.*\\)", "AsyncTask_postExecute")
  val postExecuteI: OAbsMsg = AbsMsg(CBEnter, postExecute, TopVal :: t :: v :: Nil)
}

object SJavaThreading{
  val r = NamedPureVar("r")
  val o = NamedPureVar("o")
  val runnableC = Set("java.lang.Runnable")
  val runnable = SubClassMatcher(runnableC, ".*run\\(.*\\)", "Runnable_run")
  val runnableI = AbsMsg(CBEnter, runnable, TopVal::r::Nil)
  val callableC = Set("java.util.concurrent.Callable")
  val call = SubClassMatcher(callableC, ".*call\\(.*\\)", "Callable_call")
  val callableI = AbsMsg(CBEnter, call, o::r::Nil)
}
object SDialog{
  val a = NamedPureVar("a")
  val d = NamedPureVar("d")
  val DialogC = Set("android.app.ProgressDialog","android.app.Dialog")
  //android.app.ProgressDialog: void dismiss()>()
  val dismissSignature:SignatureMatcher = SubClassMatcher(DialogC, "void dismiss\\(\\)", "Dialog_dismiss")
  // <android.app.ProgressDialog: android.app.ProgressDialog
  //     show(android.content.Context,java.lang.CharSequence,java.lang.CharSequence)>($r2, "", "");
  val showSignature:SignatureMatcher = SubClassMatcher(DialogC, ".*show.*", "Dialog_show")
  val showI = AbsMsg(CIExit, showSignature, d::TopVal::a::Nil)

  val disallowDismiss:LSSpec = LSSpec(d::Nil, a::Nil,
    And(showI, LifecycleSpec.paused),
    AbsMsg(CIEnter, dismissSignature, TopVal::d::Nil))
  val showI2 = AbsMsg(CIExit, showSignature, d::TopVal::Nil)
  val noDupeShow:LSSpec = LSSpec(d::Nil, Nil, Not(showI2), showI2)
}

//TODO: multiple signature matchers matching the same method is not supported
//object ObjectSpec {
//  val anyCb:I = I(CBEnter, SubClassMatcher("java.lang.Object", ".*", "anyMethod"), List("_"))
//  val clinitExit:I = I(CBEnter, SubClassMatcher("java.lang.Object", ".*\\<clinit\\>.*", "clinit"), List())
//  val clinitFirst:LSSpec = LSSpec(Not(anyCb),clinitExit)
//}

object Dummy{
  val a = NamedPureVar("a")
  val l = NamedPureVar("l")
  val v = NamedPureVar("v")
  val specs = Set(
    LSSpec(a::Nil, Nil, LSTrue, SpecSignatures.Activity_onCreate_entry), // Dummy onCreate to include in trace
    LSSpec(a::Nil, Nil, LSTrue, SpecSignatures.Activity_onResume_entry), // Dummy onCreate to include in trace
    LSSpec(a::Nil, Nil, LSTrue, SpecSignatures.Activity_onPause_entry), // Dummy onCreate to include in trace
    LSSpec(a::Nil, Nil, LSTrue, SpecSignatures.Activity_onDestroy_exit), // Dummy onDestroy
    LSSpec(l::Nil, Nil, LSTrue, AbsMsg(CBEnter, SpecSignatures.RxJava_call, TopVal::l::Nil)), //Dummy call
    LSSpec(v::a::Nil, Nil, LSTrue, SpecSignatures.Activity_findView_exit),
    LSSpec(v::l::Nil,Nil, LSTrue, ViewSpec.setOnClickListenerI),
    LSSpec(l::Nil, Nil, LSTrue, AbsMsg(CBEnter, ViewSpec.onClick, TopVal::l::Nil))
  )
}