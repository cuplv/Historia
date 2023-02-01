package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{AppLoc, SootWrapper}
import edu.colorado.plv.bounder.lifestate.LifeState.{LSSpec, Signature}
import edu.colorado.plv.bounder.lifestate.{FragmentGetActivityNullSpec, LifecycleSpec, RxJavaSpec, SpecSpace}
import edu.colorado.plv.bounder.symbolicexecutor.state.{CallinReturnNonNull, Qry}
import edu.colorado.plv.bounder.testutils.MkApk
import edu.colorado.plv.bounder.testutils.MkApk.makeApkWithSources
import org.scalatest.funsuite.AnyFunSuite

class DefaultAppCodeResolverTest extends AnyFunSuite {
  test("Test app code resolver can find syntactic locations of pattern misuses") {
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
        |      v.toString(); //deref2
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
        |                .subscribe(a -> {  // perhaps focus on single procedure get/use of getActivity
        |                    Activity b = getActivity();// query1
        |                    if(condition == 0){ //app code resolver analysis doesn't track this so non-deterministic
        |                     Log.i("b", b.toString()); // deref1
        |                    }else{
        |                     reqNonNull(b);
        |                    }
        |                });
        |    }
        |
        |
        |    @Override
        |    public void onDestroy(){
        |        // !!  First dereference in a basic block that is from a null field at the entry of the current method
        |        // !! fields actively set to null not in init
        |        super.onDestroy(); //perhaps focus on dereference of fields on Activities and Fragments
        |        // perhaps may be assigned/used in different callbacks
        |        // perhaps fields intentionally set to null (e.g. to avoid leaks)
        |        // pdg - program dependence graph - may help with the double dereference double counting thing?
        |        // idea: take first deref in each basic block
        |        // ~70 apps found with reasonable criteria - we randomly choose n (8ish eventually)
        |        subscription.unsubscribe(); //deref3
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
      val interpreter = config.getAbstractInterpreter
      val query1line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val query = CallinReturnNonNull(
        Signature("com.example.createdestroy.MyFragment",
          "void lambda$onActivityCreated$1$MyFragment(java.lang.Object)"), query1line,
        ".*getActivity.*")
      val resolver = interpreter.appCodeResolver
      val packageFilter = Some("com.example.createdestroy.MyFragment")
      val loc = query.make(interpreter).map{q => q.loc.asInstanceOf[AppLoc]}
      val res = resolver.allDeref(packageFilter, interpreter)
      assert(res.nonEmpty)

      val deref1Line = BounderUtil.lineForRegex(".*deref1.*".r,src)
      val deref2Line = BounderUtil.lineForRegex(".*deref2.*".r,src)
      val deref3Line = BounderUtil.lineForRegex(".*deref3.*".r,src)

      def contains(queries:Set[Qry], derefline:Int):Boolean =
        queries.exists{q => q.loc.asInstanceOf[AppLoc].line.lineNumber == derefline}

      //check that our dereferences were found
      assert(contains(res,query1line))
      assert(contains(res,deref1Line))
      assert(contains(res,deref2Line))
      assert(contains(res,deref3Line))


      val derefsFromGetActivity = resolver.derefFromCallin(
        Set(FragmentGetActivityNullSpec.getActivityNull.target),
        packageFilter,
        interpreter)
      assert(derefsFromGetActivity.nonEmpty)

      assert(contains(derefsFromGetActivity,deref1Line))
      assert(contains(derefsFromGetActivity,deref2Line))
      assert(!contains(derefsFromGetActivity,deref3Line))

      val derefsFromFields = resolver.derefFromField(packageFilter,interpreter)

      assert(contains(derefsFromFields, deref3Line))
      assert(!contains(derefsFromFields, deref2Line))
      assert(!contains(derefsFromFields, deref1Line))



    }

    makeApkWithSources(Map("MyFragment.java" -> src), MkApk.RXBase, test)
  }
}
