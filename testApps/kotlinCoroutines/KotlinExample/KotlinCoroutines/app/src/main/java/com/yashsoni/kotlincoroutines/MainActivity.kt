package com.yashsoni.kotlincoroutines

import android.os.Bundle
import android.support.v7.app.AppCompatActivity
import kotlinx.android.synthetic.main.activity_main.*
import kotlinx.coroutines.*
import okhttp3.OkHttpClient
import okhttp3.Request

class MainActivity : AppCompatActivity(), CoroutineScope by MainScope() {
    private var client = OkHttpClient()

    override fun onDestroy() {
        super.onDestroy()
        cancel()
    }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        setContentView(R.layout.activity_main)

        btn_click.setOnClickListener {
            launch {
                networkCallMain()
            }
        }
    }

    private suspend fun networkCallMain() {
        val result = networkCallHelper()
        withContext(Dispatchers.Main) {
            tv_result.text = result
        }
    }

    private suspend fun networkCallHelper(): String {
        return withContext(Dispatchers.Default) {
            val url = "http://demo2202897.mockable.io/testGet "
            val request = Request.Builder()
                .url(url)
                .build()

            val response = client.newCall(request).execute()
            return@withContext response.body()!!.string()
        }
    }
}