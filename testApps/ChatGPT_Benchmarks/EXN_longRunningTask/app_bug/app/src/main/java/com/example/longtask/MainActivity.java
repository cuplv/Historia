package com.example.longtask;

import android.app.Activity;
import android.os.Bundle;
import android.util.Log;
import android.widget.TextView;

import com.example.longtask.R;

import java.lang.reflect.Field;
import java.util.ArrayList;

import io.reactivex.Observable;
import io.reactivex.android.schedulers.AndroidSchedulers;

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
        setContentView(R.layout.activity_main);

        textView = findViewById(R.id.textView);

        // Incorrectly starting data processing on the main thread with RxJava
        processDataRxIncorrectly();
    }

    private void processDataRxIncorrectly() {
        Observable.fromCallable(() -> processLargeDataSet(loadLargeDataSet()))
                .observeOn(AndroidSchedulers.mainThread()) // Observing on the main thread
                .subscribeOn(AndroidSchedulers.mainThread()) // Incorrect: Subscribing on the main thread
                .subscribe(result -> textView.setText("Data processed successfully!"),
                        error -> textView.setText("Error processing data"));
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