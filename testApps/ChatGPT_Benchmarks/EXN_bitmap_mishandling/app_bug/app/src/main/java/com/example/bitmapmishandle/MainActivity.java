package com.example.bitmapmishandle;

import android.app.Activity;
import android.content.Context;
import android.os.Bundle;
import android.util.Log;
import android.view.View;
import android.view.ViewGroup;
import android.widget.BaseAdapter;
import android.widget.GridView;
import android.widget.ImageView;

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

    // Note: chatgpt originall stored these in an array but I changed to an ArrayList since
    //   wistoria does not handle arrays in the under approximation
//    private Integer[] imageIDs = {
//            R.drawable.image1, R.drawable.image2, R.drawable.image3,
//            R.drawable.image4, R.drawable.image5, // Assume these are large bitmap resources
//    };
    private ArrayList<Integer> imageIDs = new ArrayList<Integer>();

    {
        Log.i("histInstrumentation"," " + System.identityHashCode(imageIDs) + " = new ArrayList ");
        imageIDs.add(R.drawable.image1);
        Log.i("histInstrumentation","ci " + System.identityHashCode(imageIDs) + " ArrayList.add " + R.drawable.image1);
        imageIDs.add(R.drawable.image2);
        Log.i("histInstrumentation","ci " + System.identityHashCode(imageIDs) + " ArrayList.add " + R.drawable.image2);
        imageIDs.add(R.drawable.image3);
        Log.i("histInstrumentation","ci " + System.identityHashCode(imageIDs) + " ArrayList.add " + R.drawable.image3);
        imageIDs.add(R.drawable.image4);
        Log.i("histInstrumentation","ci " + System.identityHashCode(imageIDs) + " ArrayList.add " + R.drawable.image4);
        imageIDs.add(R.drawable.image5);
        Log.i("histInstrumentation","ci " + System.identityHashCode(imageIDs) + " ArrayList.add " + R.drawable.image5);
        // Assume these are large bitmap resources
    }

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " onCreate " + System.identityHashCode(savedInstanceState));
        super.onCreate(savedInstanceState);
        setContentView(R.layout.activity_main);
        Log.i("histInstrumentation","ci " + System.identityHashCode(this) + " setContentView " + R.layout.activity_main);

        GridView gridView = findViewById(R.id.gridView);
        Log.i("histInstrumentation",System.identityHashCode(gridView) + " = ci " + System.identityHashCode(this) + " findViewById " + R.id.gridView);
        ImageAdapter tmp1 = new ImageAdapter(this);
        Log.i("histInstrumentation"," " + System.identityHashCode(tmp1) + " = new ImageAdapter " + System.identityHashCode(this));
        gridView.setAdapter(tmp1);
        Log.i("histInstrumentation","ci " + System.identityHashCode(gridView) + " setAdapter " + System.identityHashCode(tmp1));
    }

    public class ImageAdapter extends BaseAdapter {
        private Context context;

        public ImageAdapter(Context c) {
            Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " <init> " + System.identityHashCode(c));
            context = c;
        }

        public int getCount() {
            Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " getCount ");
            return imageIDs.size();
        }

        public Object getItem(int position) {
            Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " getItem " + position);
            return position;
        }

        public long getItemId(int position) {
            Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " getItemId " + position);
            return position;
        }

        // Create a new ImageView for each item referenced by the Adapter
        public View getView(int position, View convertView, ViewGroup parent) {
            Log.i("histInstrumentation","cb " + System.identityHashCode(this) + " getView " + position + " " + System.identityHashCode(convertView) + " " + System.identityHashCode(parent));
            ImageView imageView;
            if (convertView == null) {
                imageView = new ImageView(context);
                Log.i("histInstrumentation"," " + System.identityHashCode(imageView) + " = new ImageView " + System.identityHashCode(context));
                ViewGroup.LayoutParams tmp1 = new ViewGroup.LayoutParams(350, 350);
                imageView.setLayoutParams(tmp1);
                Log.i("histInstrumentation","ci " + System.identityHashCode(imageView) + " setLayoutParams " + System.identityHashCode(tmp1));
                ImageView.ScaleType scaleType = ImageView.ScaleType.CENTER_CROP;
                imageView.setScaleType(scaleType);
                Log.i("histInstrumentation","ci " + System.identityHashCode(imageView) + " setScaleType " + System.identityHashCode(scaleType));
            } else {
                imageView = (ImageView) convertView;
            }

            Integer tmp2 = imageIDs.get(position);
            Log.i("histInstrumentation",tmp2 + " = ci " + System.identityHashCode(imageIDs) + " ArrayList.get " + position);
            imageView.setImageResource(tmp2); // Loading the full-sized image
            Log.i("histInstrumentation","ci " + System.identityHashCode(imageView) + " setImageResource " + tmp2);
            return imageView;
        }
    }

}