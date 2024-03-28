package com.example.nullptr;

import android.app.Activity;
import android.content.Intent;
import android.os.AsyncTask;
import android.os.Bundle;
import android.os.Handler;
import android.util.Log;
import android.view.View;
import android.widget.Button;
import android.widget.TextView;
import android.widget.Toast;


import org.jetbrains.annotations.Nullable;

import java.lang.reflect.Field;

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

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " onCreate");
        setContentView(R.layout.activity_main);
        Log.i("histInstrumentation","ci " + System.identityHashCode(this) + " setContentView " + R.layout.activity_main);
        launchSecondActivity();
    }

    // Method to launch SecondActivity
    public void launchSecondActivity() {
        Intent intent = new Intent(this, SecondActivity.class);
        Log.i("histInstrumentation"," " + System.identityHashCode(intent) + " = new Intent " + System.identityHashCode(this) + " " + System.identityHashCode(SecondActivity.class));
        String key = new String("extra_data");
        Log.i("histInstrumentation"," " + System.identityHashCode(key) + " = new String " + System.identityHashCode("extra_data"));
        String val = new String("Hello, SecondActivity!");
        Log.i("histInstrumentation"," " + System.identityHashCode(val) + " = new String " + System.identityHashCode("Hello, SecondActivity!"));
        intent.putExtra(key,val);
        Log.i("histInstrumentation","ci " + System.identityHashCode(intent) + " putExtra " + System.identityHashCode(key) + " " + System.identityHashCode(val));
        startActivity(intent);
        Log.i("histInstrumentation","ci " + System.identityHashCode(this) + " startActivity " + System.identityHashCode(intent));
    }

}
