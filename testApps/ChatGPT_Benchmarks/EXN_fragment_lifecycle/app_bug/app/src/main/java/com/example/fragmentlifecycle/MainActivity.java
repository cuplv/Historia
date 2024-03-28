package com.example.fragmentlifecycle;

import android.app.Activity;
import android.os.Bundle;
import android.util.Log;


import androidx.fragment.app.FragmentActivity;
import androidx.fragment.app.FragmentManager;
import androidx.fragment.app.FragmentTransaction;

import java.lang.reflect.Field;

public class MainActivity extends FragmentActivity {
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
        if (savedInstanceState == null) {
            FragmentManager tmp1 = getSupportFragmentManager();
            Log.i("histInstrumentation",System.identityHashCode(tmp1) + " = ci " + System.identityHashCode(this) + " getSupportFragmentManager ");
            FragmentTransaction tmp2 = tmp1.beginTransaction();
            Log.i("histInstrumentation",System.identityHashCode(tmp2) + " = ci " + System.identityHashCode(tmp1) + " beginTransaction ");
            ArticlesFragment tmp4 = new ArticlesFragment();
            Log.i("histInstrumentation"," " + System.identityHashCode(tmp4) + " = new ArticlesFragment ");
            FragmentTransaction tmp3 = tmp2.replace(R.id.fragment_container, tmp4);
            Log.i("histInstrumentation",System.identityHashCode(tmp3) + " = ci " + System.identityHashCode(tmp2) + " replace " + R.id.fragment_container + System.identityHashCode(tmp4));

            tmp3.commit();
            Log.i("histInstrumentation"," ci " + System.identityHashCode(tmp3) + " commit ");
        }
    }
}