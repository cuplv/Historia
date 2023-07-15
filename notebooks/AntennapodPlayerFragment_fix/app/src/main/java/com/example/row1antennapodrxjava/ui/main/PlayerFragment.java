package com.example.row1antennapodrxjava.ui.main;

import androidx.lifecycle.ViewModelProvider;

import android.app.Activity;
import android.os.Bundle;

import androidx.annotation.NonNull;
import androidx.annotation.Nullable;
import androidx.fragment.app.Fragment;

import android.util.Log;
import android.view.LayoutInflater;
import android.view.View;
import android.view.ViewGroup;

import com.example.row1antennapodrxjava.R;

import rx.Single;
import rx.Subscription;
import rx.android.schedulers.AndroidSchedulers;
import rx.functions.Action1;
import rx.schedulers.Schedulers;

public class PlayerFragment extends Fragment implements Action1<Object> {

    private Subscription sub;

    public static PlayerFragment newInstance() {
        return new PlayerFragment();
    }

    @Nullable
    @Override
    public View onCreateView(@NonNull LayoutInflater inflater, @Nullable ViewGroup container,
                             @Nullable Bundle savedInstanceState) {
        return inflater.inflate(R.layout.main_fragment, container, false);
    }

    @Override
    public void onCreate(@Nullable Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
    }

    @Override
    public void onActivityCreated(@Nullable Bundle savedInstanceState) {
        super.onActivityCreated(savedInstanceState);
        sub = Single.create(a -> {
            //try {  // uncomment to cause delay while running, useful for causing crash
            //    Thread.sleep(10000);
            //} catch (InterruptedException e) {
            //    e.printStackTrace();
            //}
            //a.onSuccess(null);
        }).subscribeOn(Schedulers.newThread())
                .observeOn(AndroidSchedulers.mainThread())
                .subscribe(this);
    }

    @Override
    public void call(Object o) {
        Activity act = getActivity();
        act.toString(); // Can this location crash?
    }
    @Override
    public void onDestroy() {
        super.onDestroy();
        sub.unsubscribe();
    }
}
