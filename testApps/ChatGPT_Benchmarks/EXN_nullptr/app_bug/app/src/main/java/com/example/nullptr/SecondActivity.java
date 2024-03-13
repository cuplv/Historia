package com.example.nullptr;

import android.app.Activity;
import android.os.Bundle;
import android.widget.TextView;

public class SecondActivity extends Activity {
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        setContentView(R.layout.activity_second);

        // Attempting to retrieve the extra data and display it
        String data = getIntent().getStringExtra("wrong_key"); // This key is incorrect
        TextView textView = findViewById(R.id.textView);
        textView.setText(data.toUpperCase()); // This line can throw a NPE if data is null
    }
}
