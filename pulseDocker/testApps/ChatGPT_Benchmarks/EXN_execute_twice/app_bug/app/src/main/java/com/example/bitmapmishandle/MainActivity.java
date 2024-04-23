package com.example.bitmapmishandle;

import android.app.Activity;
import android.app.ProgressDialog;
import android.content.Context;
import android.fake.IntArrayList;
import android.os.AsyncTask;
import android.os.Bundle;
import android.util.Log;
import android.view.View;
import android.view.ViewGroup;
import android.widget.BaseAdapter;
import android.widget.Button;
import android.widget.GridView;
import android.widget.ImageView;
import android.widget.Toast;

import com.example.bitmapmishandle.R;

import java.lang.reflect.Field;
import java.util.ArrayList;

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
    private Button startDownloadButton;
    private DownloadTask downloadTask;

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " onCreate");
        setContentView(R.layout.activity_main);
        Log.i("histInstrumentation","ci " + System.identityHashCode(this) + " setContentView " + R.layout.activity_main);

        downloadTask = new DownloadTask();
        Log.i("histInstrumentation"," " + System.identityHashCode(downloadTask) + " = new MainActivity$DownloadTask ");
        startDownloadButton = findViewById(R.id.startDownloadButton);
        Log.i("histInstrumentation",System.identityHashCode(startDownloadButton) + " = ci " + System.identityHashCode(this) + " findViewById " + R.id.startDownloadButton);

        View.OnClickListener tmp2 = new View.OnClickListener() {
            @Override
            public void onClick(View v) {
                Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " onClick " + System.identityHashCode(v));
                // Check if downloadTask is already running
                AsyncTask.Status tmp3 = downloadTask.getStatus();
                Log.i("histInstrumentation",System.identityHashCode(tmp3) + " = ci " + System.identityHashCode(downloadTask) + " getStatus ");
                if (tmp3 != AsyncTask.Status.RUNNING) {
                    // If not running, execute a new task
                    String tmp4 = "http://example.com/file.zip";
                    downloadTask.execute(tmp4);
                    Log.i("histInstrumentation", "ci " + System.identityHashCode(downloadTask) + " execute " + System.identityHashCode(tmp4));
                } else {
                    Toast.makeText(MainActivity.this, "Download already in progress", Toast.LENGTH_SHORT).show();
                    Log.i("histInstrumentation", "ci " + " makeText ");
                }

                // Attempt to reuse the same AsyncTask instance for a new download
                // This line is problematic if uncommented; it's here for demonstration.
                // downloadTask.execute("http://example.com/anotherfile.zip");
            }
        };

        startDownloadButton.setOnClickListener(tmp2);
        Log.i("histInstrumentation","ci " + System.identityHashCode(startDownloadButton) + " setOnClickListener " + System.identityHashCode(tmp2));
    }

    private static class DownloadTask extends AsyncTask<String, Integer, String> {
        @Override
        protected String doInBackground(String... urls) {
            Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " doInBackground ");
            // Simulate a download operation
            try {
                Thread.sleep(5000); // Simulate time delay of download
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
            return "Downloaded from: " + urls[0];
        }

        @Override
        protected void onPostExecute(String result) {
            Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " onPostExecute " + System.identityHashCode(result));
            super.onPostExecute(result);
            // Show download result (simplified for demonstration)
            System.out.println(result);
        }
    }

}