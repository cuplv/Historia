package com.example.longtask;

import android.app.Activity;
import android.os.Bundle;
import android.util.Log;
import android.widget.TextView;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.concurrent.Callable;
import io.reactivex.functions.Consumer;

import io.reactivex.Observable;
import io.reactivex.android.schedulers.AndroidSchedulers;
import io.reactivex.disposables.Disposable;

public class MainActivity extends Activity {
    static void dumpFields(Object o, Class clazz){
        Field[] fields = clazz.getDeclaredFields();
        for (Field field : fields) {
            field.setAccessible(true);
            try {
                Object fieldValue = field.get(o);
                Log.i("histInstrumentation", "field " + field.getName() + " " + System.identityHashCode(fieldValue));
            } catch (IllegalAccessException e) {
                throw new RuntimeException(e);
            }
        }

    }
    private TextView textView;

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " onCreate");
        setContentView(R.layout.activity_main);
        Log.i("histInstrumentation","ci " + System.identityHashCode(this) + " setContentView " + R.layout.activity_main);

        textView = findViewById(R.id.textView);
        Log.i("histInstrumentation",System.identityHashCode(textView) + " = ci " + System.identityHashCode(this) + " findViewById " + R.id.textView);

        // Incorrectly starting data processing on the main thread with RxJava
        processDataRxIncorrectly();
    }

    private void processDataRxIncorrectly() {
        Callable tmp1 = new Callable() {
            @Override
            public Object call() {
                Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " call");
                processLargeDataSet(loadLargeDataSet());
                return null;
            }
        };
        Observable tmp2 = Observable.fromCallable(tmp1);
        Log.i("histInstrumentation",System.identityHashCode(tmp2) + " = ci " + System.identityHashCode(Observable.class) + " fromCallable " + System.identityHashCode(tmp1));

        Observable tmp3 = tmp2.observeOn(AndroidSchedulers.mainThread());
        Log.i("histInstrumentation",System.identityHashCode(tmp3) + " = ci " + System.identityHashCode(tmp2) + " observeOn " + System.identityHashCode(AndroidSchedulers.mainThread()));
        Observable tmp4 = tmp3.subscribeOn(AndroidSchedulers.mainThread());
        Log.i("histInstrumentation",System.identityHashCode(tmp4) + " = ci " + System.identityHashCode(tmp3) + " subscribeOn " + System.identityHashCode(AndroidSchedulers.mainThread()));
        Consumer after = result -> textView.setText("Data processed successfully!");
        Consumer err = error -> textView.setText("Error processing data");
        Disposable tmp5 = tmp4.subscribe(after,err);
        Log.i("histInstrumentation",System.identityHashCode(tmp5) + " = ci " + System.identityHashCode(tmp4) + " subscribe " + System.identityHashCode(after) + " " + System.identityHashCode(err));
    }



    // Mock method to simulate data processing
    private String processLargeDataSet(ArrayList<String> largeDataSet) {
        // Simulate processing the dataset
        for (String item : largeDataSet) {
            // Simulate complex processing by sleeping
            try {
                Thread.sleep(10); // This sleep is just to simulate long processing
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
        return "Processed";
    }

    // Mock method to simulate loading data
    private ArrayList<String> loadLargeDataSet() {
        ArrayList<String> dataSet = new ArrayList<>();
        for (int i = 0; i < 10000; i++) {
            dataSet.add("Item " + i);
        }
        return dataSet;
    }

}