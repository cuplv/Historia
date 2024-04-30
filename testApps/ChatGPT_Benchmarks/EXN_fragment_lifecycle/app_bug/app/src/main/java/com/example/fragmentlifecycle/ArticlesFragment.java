package com.example.fragmentlifecycle;


import androidx.fragment.app.Fragment;
import android.content.Context;
import android.os.Bundle;
import android.util.Log;
import android.view.LayoutInflater;
import android.view.View;
import android.view.ViewGroup;

public class ArticlesFragment extends Fragment {

    private View rootView = null;

    @Override
    public View onCreateView(LayoutInflater inflater, ViewGroup container,
                             Bundle savedInstanceState) {
        Log.i("histInstrumentation", " cb " + System.identityHashCode(this) + " onCreateView " + System.identityHashCode(inflater) + " " + System.identityHashCode(container) );
        // Inflate the layout for this fragment
        if (rootView == null) {
            rootView = inflater.inflate(R.layout.fragment_articles, container, false);
            Log.i("histInstrumentation",System.identityHashCode(rootView) + " = ci " + System.identityHashCode(inflater) + " inflate " + R.layout.fragment_articles + System.identityHashCode(container) + " false " );
        }
        return rootView;
    }

    @Override
    public void onAttach(Context context) {
        super.onAttach(context);
        Log.i("histInstrumentation", " cb " + System.identityHashCode(this) + " onAttach " + System.identityHashCode(context));
        // Load articles assuming the context is always available
        loadArticles();
    }

    private void loadArticles() {
        // Simulate loading articles from the network or database
    }

    @Override
    public void onDestroyView() {
        super.onDestroyView();
        Log.i("histInstrumentation", " cb " + System.identityHashCode(this) + " onDestroyView " );
        // Not properly nullifying the rootView can lead to memory leaks
        // rootView = null; // Uncommenting this line is necessary to avoid leaks
    }
}