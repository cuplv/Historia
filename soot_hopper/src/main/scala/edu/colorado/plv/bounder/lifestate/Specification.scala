package edu.colorado.plv.bounder.lifestate

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{CBEnter, CBExit, CIEnter, CIExit}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, I, LSConstraint, LSFalse, LSSpec, NI, Not, Or, SetSignatureMatcher, SubClassMatcher}
import edu.colorado.plv.bounder.symbolicexecutor.state.{Equals, NotEquals}

object SpecSignatures {

  // TODO: parse specs from DSL
  // TODO: type constraints on runtime value of LS vars instead of syntactic matching of signature
  //    e.g. the following would eliminate the need for enumerating activity types
  //    I(void onActivityCreated(), _::a, a<:Activity)
  //TODO: replace SetSignatureMatcher with subtype
  val activityTypeSet = Set(
    "androidx.appcompat.app.AppCompatActivity",
    "androidx.fragment.app.FragmentActivity",
    "androidx.core.app.ComponentActivity",
    "android.app.Activity",
  )

  // Activity lifecycle
  val Activity_onResume = SubClassMatcher("android.app.Activity", "void onResume\\(\\)", "Activity_onResume")
  val Activity_onResume_entry =
    I(CBEnter, Activity_onResume, List("_", "a"))
  val Activity_onResume_exit =
    I(CBExit, Activity_onResume, List("_", "a"))
  val Activity_onCreate_exit =
    I(CBExit, SetSignatureMatcher(activityTypeSet.map((_, "void onCreate(android.os.Bundle)"))), List("_", "a"))
//  val Activity_onPause_entry = I(CBEnter, SetSignatureMatcher(activityTypeSet.map((_, "void onPause()"))), List("_", "a"))
//  val Activity_onPause_exit = I(CBExit, SetSignatureMatcher(activityTypeSet.map((_, "void onPause()"))), List("_", "a"))
  val Activity_onPause = SubClassMatcher("android.app.Activity","void onPause\\(\\)", "Activity_onPause")
  val Activity_onPause_entry = I(CBEnter, Activity_onPause, List("_", "a"))
  val Activity_onPause_exit = I(CBExit, Activity_onPause, List("_", "a"))
  val Activity_init_exit = I(CBExit,
    SetSignatureMatcher((activityTypeSet + "java.lang.Object").map((_, "void <init>()"))), List("_", "a"))

  val Activity_init_entry: I = Activity_init_exit.copy(mt = CBEnter)

  // Fragment getActivity
  val Fragment_getActivity_Signatures = SetSignatureMatcher(Set(
    ("android.app.Fragment","android.app.Activity getActivity()"),
    ("android.support.v4.app.Fragment","android.support.v4.app.FragmentActivity getActivity()"),
    ("android.support.v4.app.FragmentHostCallback","android.app.Activity getActivity()"),
    ("androidx.fragment.app.Fragment","androidx.fragment.app.FragmentActivity getActivity()")
  ))
  val Fragment_get_activity_exit_null = I(CIExit, Fragment_getActivity_Signatures, "@null"::"f"::Nil)

  val Fragment_get_activity_exit = I(CIExit, Fragment_getActivity_Signatures, "a"::"f"::Nil)

  val Fragment_onActivityCreated_Signatures = SetSignatureMatcher(Set(
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
  ))

  val Fragment_onActivityCreated_entry = I(CBEnter, Fragment_onActivityCreated_Signatures, "_"::"f"::Nil)

  val Fragment_onDestroy_Signatures = SetSignatureMatcher(Set(
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
  ))
  val Fragment_onDestroy_exit = I(CBExit, Fragment_onDestroy_Signatures, "_"::"f"::Nil)

  // rxjava
  val RxJava_call = SetSignatureMatcher(Set(
    ("rx.functions.Action1","void call(java.lang.Object)"),
  ))
  val RxJava_call_entry = I(CBEnter, RxJava_call, "_"::"l"::Nil)

  val RxJava_unsubscribe = SetSignatureMatcher(Set(
    ("retrofit2.adapter.rxjava.CallArbiter","void unsubscribe()"),
    ("rx.SingleSubscriber","void unsubscribe()"),
    ("rx.Subscriber","void unsubscribe()"),
    ("rx.Subscription","void unsubscribe()"),
    ("rx.android.schedulers.LooperScheduler$HandlerWorker","void unsubscribe()"),
    ("rx.android.schedulers.LooperScheduler$ScheduledAction","void unsubscribe()"),
    ("rx.internal.operators.CachedObservable$ReplayProducer","void unsubscribe()"),
    ("rx.internal.operators.CompletableFromEmitter$FromEmitter","void unsubscribe()"),
    ("rx.internal.operators.OnSubscribeAmb","void unsubscribeAmbSubscribers(java.util.Collection)"),
    ("rx.internal.operators.OnSubscribeAmb$Selection","void unsubscribeLosers()"),
    ("rx.internal.operators.OnSubscribeAmb$Selection","void unsubscribeOthers(rx.internal.operators.OnSubscribeAmb$AmbSubscriber)"),
    ("rx.internal.operators.OnSubscribeCombineLatest$LatestCoordinator","void unsubscribe()"),
    ("rx.internal.operators.OnSubscribeCreate$BaseEmitter","void unsubscribe()"),
    ("rx.internal.operators.OnSubscribeDetach$DetachProducer","void unsubscribe()"),
    ("rx.internal.operators.OnSubscribeFlatMapCompletable$FlatMapCompletableSubscriber$InnerSubscriber","void unsubscribe()"),
    ("rx.internal.operators.OnSubscribeFlatMapSingle$FlatMapSingleSubscriber$Requested","void unsubscribe()"),
    ("rx.internal.operators.OnSubscribeGroupJoin$ResultManager","void unsubscribe()"),
    ("rx.internal.operators.OnSubscribePublishMulticast","void unsubscribe()"),
    ("rx.internal.operators.OnSubscribePublishMulticast$PublishProducer","void unsubscribe()"),
    ("rx.internal.operators.OnSubscribeUsing$DisposeAction","void unsubscribe()"),
    ("rx.internal.operators.OperatorGroupBy$State","void unsubscribe()"),
    ("rx.internal.operators.OperatorGroupByEvicting$State","void unsubscribe()"),
    ("rx.internal.operators.OperatorOnBackpressureLatest$LatestEmitter","void unsubscribe()"),
    ("rx.internal.operators.OperatorPublish$InnerProducer","void unsubscribe()"),
    ("rx.internal.operators.OperatorReplay","void unsubscribe()"),
    ("rx.internal.operators.OperatorReplay$InnerProducer","void unsubscribe()"),
    ("rx.internal.operators.SingleFromEmitter$SingleEmitterImpl","void unsubscribe()"),
    ("rx.internal.schedulers.CachedThreadScheduler$EventLoopWorker","void unsubscribe()"),
    ("rx.internal.schedulers.EventLoopsScheduler$EventLoopWorker","void unsubscribe()"),
    ("rx.internal.schedulers.ExecutorScheduler$ExecutorSchedulerWorker","void unsubscribe()"),
    ("rx.internal.schedulers.ImmediateScheduler$InnerImmediateScheduler","void unsubscribe()"),
    ("rx.internal.schedulers.NewThreadWorker","void unsubscribe()"),
    ("rx.internal.schedulers.ScheduledAction","void unsubscribe()"),
    ("rx.internal.schedulers.ScheduledAction$FutureCompleter","void unsubscribe()"),
    ("rx.internal.schedulers.ScheduledAction$Remover","void unsubscribe()"),
    ("rx.internal.schedulers.ScheduledAction$Remover2","void unsubscribe()"),
    ("rx.internal.schedulers.SchedulerWhen","void unsubscribe()"),
    ("rx.internal.schedulers.SchedulerWhen$2","void unsubscribe()"),
    ("rx.internal.schedulers.SchedulerWhen$3","void unsubscribe()"),
    ("rx.internal.schedulers.SchedulerWhen$ScheduledAction","void unsubscribe()"),
    ("rx.internal.schedulers.TrampolineScheduler$InnerCurrentThreadScheduler","void unsubscribe()"),
    ("rx.internal.subscriptions.CancellableSubscription","void unsubscribe()"),
    ("rx.internal.subscriptions.SequentialSubscription","void unsubscribe()"),
    ("rx.internal.subscriptions.Unsubscribed","void unsubscribe()"),
    ("rx.internal.util.IndexedRingBuffer","void unsubscribe()"),
    ("rx.internal.util.RxRingBuffer","void unsubscribe()"),
    ("rx.internal.util.SubscriptionList","void unsubscribe()"),
    ("rx.internal.util.SubscriptionList","void unsubscribeFromAll(java.util.Collection)"),
    ("rx.internal.util.SynchronizedSubscription","void unsubscribe()"),
    ("rx.observables.AsyncOnSubscribe$AsyncOuterManager","void unsubscribe()"),
    ("rx.observables.SyncOnSubscribe$SubscriptionProducer","void unsubscribe()"),
    ("rx.observers.AsyncCompletableSubscriber$Unsubscribed","void unsubscribe()"),
    ("rx.observers.SafeCompletableSubscriber","void unsubscribe()"),
    ("rx.schedulers.TestScheduler$InnerTestScheduler","void unsubscribe()"),
    ("rx.subjects.PublishSubject$PublishSubjectProducer","void unsubscribe()"),
    ("rx.subjects.ReplaySubject$ReplayProducer","void unsubscribe()"),
    ("rx.subjects.UnicastSubject$State","void unsubscribe()"),
    ("rx.subscriptions.BooleanSubscription","void unsubscribe()"),
    ("rx.subscriptions.CompositeSubscription","void unsubscribe()"),
    ("rx.subscriptions.CompositeSubscription","void unsubscribeFromAll(java.util.Collection)"),
    ("rx.subscriptions.MultipleAssignmentSubscription","void unsubscribe()"),
    ("rx.subscriptions.MultipleAssignmentSubscription$State","rx.subscriptions.MultipleAssignmentSubscription$State unsubscribe()"),
    ("rx.subscriptions.RefCountSubscription","void unsubscribe()"),
    ("rx.subscriptions.RefCountSubscription","void unsubscribeAChild()"),
    ("rx.subscriptions.RefCountSubscription","void unsubscribeActualIfApplicable(rx.subscriptions.RefCountSubscription$State)"),
    ("rx.subscriptions.RefCountSubscription$InnerSubscription","void unsubscribe()"),
    ("rx.subscriptions.RefCountSubscription$State","rx.subscriptions.RefCountSubscription$State unsubscribe()"),
    ("rx.subscriptions.SerialSubscription","void unsubscribe()"),
    ("rx.subscriptions.SerialSubscription$State","rx.subscriptions.SerialSubscription$State unsubscribe()"),
    ("rx.subscriptions.Subscriptions","rx.Subscription unsubscribed()"),
    ("rx.subscriptions.Subscriptions$FutureSubscription","void unsubscribe()"),
    ("rx.subscriptions.Subscriptions$Unsubscribed","void unsubscribe()"),
  ))
  val RxJava_unsubscribe_exit = I(CIExit, RxJava_unsubscribe, "_"::"s"::Nil)

  val RxJava_subscribe = SetSignatureMatcher(Set(
    ("rx.Single", "rx.Subscription subscribe(rx.functions.Action1)")
  ))
  val RxJava_subscribe_exit = I(CIExit, RxJava_subscribe, "s"::"_"::"l"::Nil)
  val RxJava_subscribe_exit_null = RxJava_subscribe_exit.copy(lsVars = "@null"::Nil)
}

object FragmentGetActivityNullSpec{
//  val cond = Or(Not(SpecSignatures.Fragment_onActivityCreated_entry), SpecSignatures.Fragment_onDestroy_exit)
  val cond = NI(SpecSignatures.Fragment_onDestroy_exit, SpecSignatures.Fragment_onActivityCreated_entry)
  val getActivityNull = LSSpec(cond, SpecSignatures.Fragment_get_activity_exit_null)
  val getActivityNonNull = LSSpec(Not(cond), SpecSignatures.Fragment_get_activity_exit,
    Set(LSConstraint("a", NotEquals, "@null")))
}

object RxJavaSpec{
  val subUnsub = NI(
    SpecSignatures.RxJava_subscribe_exit,
    SpecSignatures.RxJava_unsubscribe_exit)
  val call = LSSpec(subUnsub, SpecSignatures.RxJava_call_entry)
//  val subscribeDoesNotReturnNull = LSSpec(LSFalse, SpecSignatures.RxJava_subscribe_exit_null)
  val subscribeIsUnique = LSSpec(Not(SpecSignatures.RxJava_subscribe_exit.copy(lsVars = "s"::Nil)),
    SpecSignatures.RxJava_subscribe_exit) //,Set(LSConstraint("s",NotEquals,"@null")  )
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

  val Fragment_activityCreatedOnlyFirst = LSSpec(
    And(
      Not(SpecSignatures.Fragment_onDestroy_exit),
      Not(SpecSignatures.Fragment_onActivityCreated_entry)
    ),
    SpecSignatures.Fragment_onActivityCreated_entry)
  val spec = new SpecSpace(Set(onPause_onlyafter_onResume_init, onPause_onlyafter_onResume_init, init_first_callback))
}