package com.example.row5antennapodsynchnull;

import androidx.appcompat.app.AppCompatActivity;

import android.os.Bundle;
import android.util.Log;
import android.view.View;
import android.widget.Button;

import com.example.row5antennapodsynchnull.ui.main.ChaptersFragment;

public class MainActivity extends AppCompatActivity {

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        Log.i("MainActivity", "onCreate");
        super.onCreate(savedInstanceState);
        setContentView(R.layout.main_activity);

    }
    @Override
    protected void onResume(){
       super.onResume();
        Button b = findViewById(R.id.button);
        b.setOnClickListener(new View.OnClickListener() {
            @Override
            public void onClick(View view) {
                setContentView(R.layout.main_activity);
                getSupportFragmentManager().beginTransaction()
                        .replace(R.id.container, new ChaptersFragment())
                        .commitNow();
            }
        });
    }
    @Override
    protected void onDestroy() {
        super.onDestroy();
        Log.i("MainActivity", "onDestroy");
    }
}
