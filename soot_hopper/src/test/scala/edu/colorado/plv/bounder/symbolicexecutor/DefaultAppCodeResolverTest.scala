package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{AppLoc, SootWrapper}
import edu.colorado.plv.bounder.lifestate.LifeState.{LSSpec, Signature}
import edu.colorado.plv.bounder.lifestate.{FragmentGetActivityNullSpec, SpecSpace}
import edu.colorado.plv.bounder.symbolicexecutor.state.{CallinReturnNonNull, Qry, Reachable}
import edu.colorado.plv.bounder.testutils.MkApk
import edu.colorado.plv.bounder.testutils.MkApk.makeApkWithSources
import org.scalatest.funsuite.AnyFunSuite

class DefaultAppCodeResolverTest extends AnyFunSuite {
  def srcAct(withFinish:String)  =
    s"""package com.example.createdestroy;
      |import android.app.Activity;
      |import android.os.AsyncTask;
      |import android.view.View.OnClickListener;
      |import android.widget.Button;
      |import android.view.View;
      |public class MyActivity extends Activity implements OnClickListener {
      |   Object target = null;
      |   @Override
      |   public void onResume(){
      |      target = new Object();
      |      super.onPause();
      |      Button b = findViewById(42);
      |      b.setOnClickListener(this);
      |   }
      |   @Override
      |   public void onClick(View v){
      |     target.toString(); //query1
      |     ${withFinish}
      |   }
      |   @Override
      |   public void onPause(){
      |     super.onPause();
      |     target = null;
      |   }
      |}
      |""".stripMargin
  test("Heuristic deref null sync"){
    List(("finish();",None),("",None)).foreach {case (finishLine, expected) =>
      val src = srcAct(finishLine)
      val test: String => Unit = apk => {
        val query1Line = BounderUtil.lineForRegex(".*query1.*".r, src)
        val specSpace = new SpecSpace(Set.empty)
        val w = new SootWrapper(apk, Set.empty)
        val config = ExecutorConfig(
          stepLimit = 2000, w, specSpace,
          component = Some(List("com.example.createdestroy.*")))
        val interp = config.getAbstractInterpreter

        val initialQuery = Reachable(Signature( "com.example.createdestroy.MyActivity", "void onClick(android.view.View)"),
          query1Line)
        val query = initialQuery.make(interp)
        assert(query.nonEmpty)

        assert(apk != null)
        ???
      }

      makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
    }
  }
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
        |    static Object foo = new Object();
        |
        |    public MyFragment() {
        |        // Required empty public constructor
        |    }
        |
        |    private void reqNonNull(Object v){
        |      v.toString(); //deref2 //note: heuristic search won't find this one because contained in separate block
        |      foo.toString(); //deref4
        |    }
        |    @Override
        |    public void onActivityCreated(Bundle savedInstanceState){
        |        foo = null;
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
        |        subscription = null;
        |        getActivity(); // check for bug where no assign crashes heuristic find
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

      // Use Historia to find derefs
      val res = resolver.allDeref(packageFilter, interpreter)
      assert(res.nonEmpty)

      val deref1Line = BounderUtil.lineForRegex(".*deref1.*".r,src)
      val deref2Line = BounderUtil.lineForRegex(".*deref2.*".r,src)
      val deref3Line = BounderUtil.lineForRegex(".*deref3.*".r,src)
      val deref4Line = BounderUtil.lineForRegex(".*deref4.*".r,src)

      def contains(queries:Set[Qry], derefline:Int):Boolean =
        queries.exists{q => q.loc.asInstanceOf[AppLoc].line.lineNumber == derefline}

      //check that our dereferences were found
      assert(contains(res,query1line))
      assert(contains(res,deref1Line))
      assert(contains(res,deref2Line))
      assert(contains(res,deref3Line))


      val getActNullAbsMsg = Set(FragmentGetActivityNullSpec.getActivityNull.target)
      val derefsFromGetActivity = resolver.derefFromCallin(
        getActNullAbsMsg,
        packageFilter,
        interpreter)
      assert(derefsFromGetActivity.nonEmpty)

      assert(contains(derefsFromGetActivity.flatMap(_.make(interpreter)),deref1Line))
      assert(contains(derefsFromGetActivity.flatMap(_.make(interpreter)),deref2Line))
      assert(!contains(derefsFromGetActivity.flatMap(_.make(interpreter)),deref3Line))

      val derefsFromFields = resolver.derefFromField(packageFilter,interpreter)

      assert(contains(derefsFromFields, deref3Line))
      assert(!contains(derefsFromFields, deref2Line))
      assert(!contains(derefsFromFields, deref1Line))

      // Heuristic find deref - basic blocks that read and dereference fields that may be set to null elsewhere
      val heuristicLocations = resolver.heuristicDerefNull(packageFilter, interpreter, _ => true)
      assert(contains(heuristicLocations.flatMap(_.make(interpreter)), deref3Line))
      assert(contains(heuristicLocations.flatMap(_.make(interpreter)), deref4Line))
      assert(!contains(heuristicLocations.flatMap(_.make(interpreter)), deref1Line))

      //heuristic find getAct derefs
      val heuristicGetActDerefs =
        resolver.heuristicCbFlowsToDeref(getActNullAbsMsg, packageFilter, interpreter)
      assert(contains(heuristicGetActDerefs.flatMap(_.make(interpreter)), deref1Line))
      assert(!contains(heuristicGetActDerefs.flatMap(_.make(interpreter)), deref3Line))
      assert(!contains(heuristicGetActDerefs.flatMap(_.make(interpreter)), deref4Line))
      //Note: not checking for deref2Line because heuristic is not inter-procedural

    }

    makeApkWithSources(Map("MyFragment.java" -> src), MkApk.RXBase, test)
  }
}
