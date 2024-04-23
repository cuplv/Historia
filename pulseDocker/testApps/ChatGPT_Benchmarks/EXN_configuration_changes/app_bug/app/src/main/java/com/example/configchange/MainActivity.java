package com.example.configchange;

import android.app.Activity;
import android.os.Bundle;
import android.util.Log;
import android.widget.EditText;
import android.widget.TextView;

import com.android.volley.Request;
import com.android.volley.RequestQueue;
import com.android.volley.Response;
import com.android.volley.VolleyError;
import com.android.volley.toolbox.StringRequest;
import com.android.volley.toolbox.Volley;

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
    private EditText usernameInput;
    private EditText emailInput;

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " onCreate");
        setContentView(R.layout.activity_main);
        Log.i("histInstrumentation","ci " + System.identityHashCode(this) + " setContentView " + R.layout.activity_main);

        usernameInput = findViewById(R.id.usernameInput);
        Log.i("histInstrumentation",System.identityHashCode(usernameInput) + " = ci " + System.identityHashCode(this) + " findViewById " + R.id.usernameInput);
        emailInput = findViewById(R.id.emailInput);
        Log.i("histInstrumentation",System.identityHashCode(emailInput) + " = ci " + System.identityHashCode(this) + " findViewById " + R.id.emailInput);
        // Initialize other fields here

        // No handling of savedInstanceState to restore state
    }

    @Override
    protected void onDestroy() {
        super.onDestroy();
        Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " onDestroy");
    }

}