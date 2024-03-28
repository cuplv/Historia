package com.example.networkfailure;

import android.util.Log;

import com.android.volley.Response;
import com.android.volley.VolleyError;

public class MyErrorListener implements Response.ErrorListener {
    MyErrorListener(){
        //stub
    }
    @Override
    public void onErrorResponse(VolleyError error) {
        Log.i("histInstrumentation", "cb " + System.identityHashCode(this) + " onErrorResponse " + System.identityHashCode(error));
        // Here should be the error handling code, but it's missing.
        // In a real-world scenario, you would handle the error appropriately.
    }
}