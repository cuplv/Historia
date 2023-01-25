package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{AppLoc, SootWrapper}
import edu.colorado.plv.bounder.lifestate.LifeState.{LSSpec, Signature}
import edu.colorado.plv.bounder.lifestate.{FragmentGetActivityNullSpec, LifecycleSpec, RxJavaSpec, SpecSpace}
import edu.colorado.plv.bounder.symbolicexecutor.state.CallinReturnNonNull
import edu.colorado.plv.bounder.testutils.MkApk
import edu.colorado.plv.bounder.testutils.MkApk.makeApkWithSources
import org.scalatest.funsuite.AnyFunSuite

class DefaultAppCodeResolverTest extends AnyFunSuite {
  test("Test app code resolver finds flow from getActivity to dereference") {
    //TODO: this functionality is not complete
    val src =
      """
        |package com.example.createdestroy;
        |import android.app.Activity;
        |import android.content.Context;
        |import android.net.Uri;
        |import android.os.Bundle;
        |
        |import androidx.fragment.app.Fragment;
        |
        |import android.util.Log;
        |import android.view.LayoutInflater;
        |import android.view.View;
        |import android.view.ViewGroup;
        |
        |import rx.Single;
        |import rx.Subscription;
        |import rx.android.schedulers.AndroidSchedulers;
        |import rx.schedulers.Schedulers;
        |
        |
        |public class MyFragment extends Fragment {
        |    Subscription subscription;
        |    int condition = 0;
        |
        |    public MyFragment() {
        |        // Required empty public constructor
        |    }
        |
        |    private void reqNonNull(Object v){
        |      v.toString();
        |    }
        |    @Override
        |    public void onActivityCreated(Bundle savedInstanceState){
        |        super.onActivityCreated(savedInstanceState);
        |        subscription = Single.create(subscriber -> {
        |            try {
        |                Thread.sleep(2000);
        |            } catch (InterruptedException e) {
        |                e.printStackTrace();
        |            }
        |            subscriber.onSuccess(3);
        |        })
        |                .subscribeOn(Schedulers.newThread())
        |                .observeOn(AndroidSchedulers.mainThread())
        |                .subscribe(a -> {
        |                    Activity b = getActivity();// query1
        |                    if(condition == 0){ //app code resolver analysis doesn't track this so non-deterministic
        |                     Log.i("b", b.toString());
        |                    }else{
        |                     reqNonNull(b);
        |                    }
        |                });
        |    }
        |
        |
        |    @Override
        |    public void onDestroy(){
        |        super.onDestroy();
        |        subscription.unsubscribe();
        |    }
        |}
        |""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set[LSSpec]()
      val w = new SootWrapper(apk, specs)
      val specSpace = new SpecSpace(specs)
      val config = ExecutorConfig(
        stepLimit = 300, w, specSpace,
        component = Some(List("com.example.createdestroy.MyFragment.*")),
        printAAProgress = true)
      val symbolicExecutor = config.getAbstractInterpreter
      val query = CallinReturnNonNull(
        Signature("com.example.createdestroy.MyFragment",
          "void lambda$onActivityCreated$1$MyFragment(java.lang.Object)"), BounderUtil.lineForRegex(".*query1.*".r, src),
        ".*getActivity.*")
      val resolver = symbolicExecutor.appCodeResolver
      val loc = query.make(symbolicExecutor).map{q => q.loc.asInstanceOf[AppLoc]}
      val res = resolver.nullValueMayFlowTo(loc, symbolicExecutor.controlFlowResolver)
      assert(res.nonEmpty)

    }

    makeApkWithSources(Map("MyFragment.java" -> src), MkApk.RXBase, test)
  }
}
