package com.example.activityleak;


import android.os.Bundle;
import android.app.Activity;
import android.util.Log;

import java.lang.reflect.Field;
import java.lang.reflect.RecordComponent;
import java.util.ArrayList;
import java.util.List;

public class LeakActivity extends Activity {
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

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " onCreate");

        // Starting a long-running thread with an inner class holding a reference to the Activity
        Runnable tmp = new Runnable() {
            @Override
            public void run() {
                // Simulate long-running task
                try {
                    Thread.sleep(5000); // Sleep for 100 seconds
                } catch (InterruptedException e) {
                    e.printStackTrace();
                }
                Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " run");
                dumpFields(this, this.getClass());
            }
        };
        Log.i("histInstrumentation"," " + System.identityHashCode(tmp) + " = new Runnable$1 " + System.identityHashCode(this));
        Thread tmp2 = new Thread(tmp);
        Log.i("histInstrumentation"," " + System.identityHashCode(tmp2) + " = new Thread " + System.identityHashCode(this));
        tmp2.start();
        Log.i("histInstrumentation","ci " + System.identityHashCode(tmp2) + " start");
    }
    @Override
    protected void onDestroy(){
        Log.i("histInstrumentation","cb " + System.identityHashCode(this) + "onDestroy");
        super.onDestroy();
    }
}