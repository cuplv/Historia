package com.example.networkfailure;

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
    private TextView textView;

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " onCreate");
        setContentView(R.layout.activity_main);
        Log.i("histInstrumentation","ci " + System.identityHashCode(this) + " setContentView " + R.layout.activity_main);
        textView = findViewById(R.id.textView);
        Log.i("histInstrumentation",System.identityHashCode(textView) + " = ci " + System.identityHashCode(this) + " findViewById " + R.id.textView);

        fetchUserData();
    }
    private void fetchUserData() {
        String url = new String("https://nonexistantlink.io");
        Log.i("histInstrumentation"," " + System.identityHashCode(url) + " = new String " + System.identityHashCode("https://nonexistantlink.io"));
        // Instantiate the RequestQueue.
        RequestQueue queue = Volley.newRequestQueue(this);
        Log.i("histInstrumentation", " ci " + System.identityHashCode(Volley.class) + " new RequestQueue " + System.identityHashCode(this));

        Response.ErrorListener errorListener = new MyErrorListener();
        Log.i("histInstrumentation"," "+System.identityHashCode(errorListener)+" = new MyErrorListener ");

        Response.Listener<String> responseListener = new Response.Listener<String>() {
            @Override
            public void onResponse(String response) {
                Log.i("histInstrumentation", "cb " + System.identityHashCode(this) + " onResponse " + System.identityHashCode(response));
                // Display the first 500 characters of the response string.
                String text = response.substring(0, 500);
                Log.i("histInstrumentation", System.identityHashCode(text) + " = ci " + System.identityHashCode(response) + " substring " + 0 + " " + 500);
                textView.setText(text);
                Log.i("histInstrumentation", " ci " + System.identityHashCode(textView) + " setText " + System.identityHashCode(text));
            }
        };
        //Log.i("histInstrumentation"," "+System.identityHashCode(responseListener)+" = new MyListener ");
            // Request a string response from the provided URL.
            StringRequest stringRequest = new StringRequest(Request.Method.GET, url,
                    responseListener, errorListener);
        Log.i("histInstrumentation"," "+System.identityHashCode(stringRequest)+" = new StringRequest "+
                    System.identityHashCode(Request.Method.GET)+" "+System.identityHashCode(url)+" "+
                    System.identityHashCode(responseListener)+" "+System.identityHashCode(errorListener));

            // Add the request to the RequestQueue.
        queue.add(stringRequest);
        Log.i("histInstrumentation"," ci "+System.identityHashCode(queue)+" add "+System.identityHashCode(stringRequest));
        };
}