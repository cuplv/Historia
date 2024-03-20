package com.example.inefficientnetwork;

import android.app.Activity;
import android.os.Bundle;
import android.util.Log;
import android.widget.ArrayAdapter;
import android.widget.ListView;
import android.widget.TextView;

import com.android.volley.Request;
import com.android.volley.RequestQueue;
import com.android.volley.Response;
import com.android.volley.VolleyError;
import com.android.volley.toolbox.StringRequest;
import com.android.volley.toolbox.Volley;

import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;

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
    private ListView listView;
    private TextView textView;
    private ArrayList<String> titles = new ArrayList<>();
    private ArrayAdapter<String> adapter;

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " onCreate");
        setContentView(R.layout.activity_main);
        Log.i("histInstrumentation","ci " + System.identityHashCode(this) + " setContentView " + R.layout.activity_main);

        listView = findViewById(R.id.listView);
        Log.i("histInstrumentation",System.identityHashCode(listView) + " = ci " + System.identityHashCode(this) + " findViewById " + R.id.listView);
        adapter = new ArrayAdapter<>(this, android.R.layout.simple_list_item_1, titles);
        textView = findViewById(R.id.textView);
        listView.setAdapter(adapter);

        fetchArticles();
    }

    @Override
    protected void onResume() {
        super.onResume();
        Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " onResume");
        fetchArticles(); // Inefficiently fetches articles every time the activity resumes
    }
    private void fetchArticles() {
        textView.setText("h");
        String url = new String("https://jsonplaceholder.typicode.com/posts/");
        Log.i("histInstrumentation"," " + System.identityHashCode(url) + " = new String " + System.identityHashCode("https://www.google.com/search?q=android"));

        RequestQueue queue = Volley.newRequestQueue(this);
        Log.i("histInstrumentation",System.identityHashCode(queue) + " = ci " + System.identityHashCode(Volley.class) + " newRequestQueue " + System.identityHashCode(this));
        Response.Listener<String> tmp1 = new Response.Listener<String>() {
            @Override
            public void onResponse(String response) {
                Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " onResponse " + System.identityHashCode(response));
                try {
                    JSONArray jsonArray = new JSONArray(response);
                    titles.clear();
                    for (int i = 0; i < jsonArray.length(); i++) {
                        JSONObject jsonObject = jsonArray.getJSONObject(i);
                        titles.add(jsonObject.getString("title"));
                    }
                    adapter.notifyDataSetChanged();
                } catch (JSONException e) {
                    e.printStackTrace();
                }
            }
        };
        Response.ErrorListener tmp2 = new Response.ErrorListener() {
            @Override
            public void onErrorResponse(VolleyError error) {
                Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " onErrorResponse " + System.identityHashCode(error) );
                // Handle error
            }
        };
        StringRequest stringRequest = new StringRequest(Request.Method.GET, url,
                tmp1, tmp2);
        Log.i("histInstrumentation"," " + System.identityHashCode(stringRequest) + " = new StringRequest "
                + System.identityHashCode(Request.Method.GET) + " "
                + System.identityHashCode(url) + " "
                + System.identityHashCode(tmp1) + " "
                + System.identityHashCode(tmp2));

        queue.add(stringRequest);
        Log.i("histInstrumentation","ci " + System.identityHashCode(queue) + " add " + System.identityHashCode(stringRequest));
    }

}