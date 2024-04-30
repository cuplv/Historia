package com.example.nullptr;

import android.app.Activity;
import android.content.Intent;
import android.os.Bundle;
import android.util.Log;
import android.widget.TextView;

public class SecondActivity extends Activity {
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " onCreate");
        setContentView(R.layout.activity_second);
        Log.i("histInstrumentation","ci " + System.identityHashCode(this) + " setContentView " + R.layout.activity_second);

        // Attempting to retrieve the extra data and display it
        Intent tmp1 = getIntent();
        Log.i("histInstrumentation",System.identityHashCode(tmp1) + " = ci " + System.identityHashCode(this) + " getIntent " );
        String key = new String("wrong_key");
        Log.i("histInstrumentation"," " + System.identityHashCode(key) + " = new String " + System.identityHashCode("wrong_key"));
        String data = tmp1.getStringExtra(key); // This key is incorrect
        Log.i("histInstrumentation",System.identityHashCode(data) + " = ci " + System.identityHashCode(tmp1) + " getStringExtra " + System.identityHashCode(key) );
        TextView textView = findViewById(R.id.textView);
        Log.i("histInstrumentation",System.identityHashCode(textView) + " = ci " + System.identityHashCode(this) + " findViewById " + R.id.textView );
        String tmp2 = data.toUpperCase(); // This line can throw a NPE if data is null
        Log.i("histInstrumentation",System.identityHashCode(tmp2) + " = ci " + System.identityHashCode(data) + " toUpperCase " );
        textView.setText(tmp2);
        Log.i("histInstrumentation"," ci " + System.identityHashCode(textView) + " setText " + System.identityHashCode(tmp2) );
    }
}
