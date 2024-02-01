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

import rx.Scheduler;
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
        Log.w("traceinst","cb " + System.identityHashCode(this) + " PlayerFragment.onActivityCreated" );
        super.onActivityCreated(savedInstanceState);

        Single<Object> creRes = Single.create(a -> {
            try {  // uncomment to cause delay while running, useful for causing crash
                Thread.sleep(10000);
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
            Log.w("traceinst","ci " + System.identityHashCode(a) + " onSuccess" );
            a.onSuccess(null);
        });
        Log.w("traceinst",System.identityHashCode(creRes) + " = ci" + " Single.create " );

        Scheduler newThread = Schedulers.newThread();
        Scheduler mainThread = AndroidSchedulers.mainThread();
        Log.w("traceinst","ci " + System.identityHashCode(creRes) + " subscribeOn " + System.identityHashCode(newThread) );
        Log.w("traceinst","ci " + System.identityHashCode(creRes) + " observeOn " + System.identityHashCode(mainThread) );
        Single<Object> obsRes = creRes.subscribeOn(newThread)
                .observeOn(mainThread);
        sub = obsRes.subscribe(this);
        Log.w("traceinst",System.identityHashCode(sub) + " = ci " + System.identityHashCode(obsRes) + " subscribe " + System.identityHashCode(this));
        Log.w("traceinst","cbret " + System.identityHashCode(this) + " PlayerFragment.onActivityCreated" );
    }

    @Override
    public void call(Object o) {
        Log.w("traceinst","cb " + System.identityHashCode(this) + " PlayerFragment.call" );
        Activity act = getActivity();
        Log.w("traceinst",System.identityHashCode(act) + " = ci " + System.identityHashCode(this) + " getActivity" );
        act.toString(); // Can this location crash?
        Log.w("traceinst","cbret " + System.identityHashCode(this) + " PlayerFragment.call" );
    }
    @Override
    public void onDestroy() {
        Log.w("traceinst","cb " + System.identityHashCode(this) + " PlayerFragment.onDestroy" );
        super.onDestroy();
        //sub.unsubscribe();
        Log.w("traceinst","cbret " + System.identityHashCode(this) + " PlayerFragment.onDestroy" );
    }
}
