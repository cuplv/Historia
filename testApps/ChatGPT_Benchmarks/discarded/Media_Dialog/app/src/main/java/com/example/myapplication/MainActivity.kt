package com.example.myapplication

import android.app.Activity
import android.app.AlertDialog
import android.net.Uri
import android.os.Bundle
import android.util.Log
import com.google.android.exoplayer2.ExoPlayer
import com.google.android.exoplayer2.MediaItem
import com.google.android.exoplayer2.Player
import com.google.android.exoplayer2.util.MimeTypes

class MainActivity : Activity() {
    private lateinit var player: ExoPlayer
    private lateinit var alertDialog: AlertDialog

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        Log.i("onCreate", "onCreate" + System.identityHashCode(this))

        // Initialize player
        player = ExoPlayer.Builder(this).build()

        // Prepare media item
        val builder = MediaItem.Builder()
        builder.setUri(Uri.parse("https://www2.cs.uic.edu/~i101/SoundFiles/CantinaBand3.wav"))
        builder.setMimeType(MimeTypes.BASE_TYPE_AUDIO)
        val mediaItem = builder.build()
        player.setMediaItem(mediaItem)
        player.prepare()

        // Show AlertDialog
        showAlertDialog()

        // Listen for playback completion
        player.addListener(object : Player.Listener {
            override fun onPlaybackStateChanged(state: Int) {
                Log.i("done playing", "done playing" + System.identityHashCode(this@MainActivity))
                if (state == Player.STATE_ENDED) {
                    Log.i("dismissing", "dismissing")
                    // Dismiss AlertDialog
                    alertDialog.dismiss()
                }
            }
        })

        // Start playback
        player.play()
    }

    private fun showAlertDialog() {

        Log.i("showAlertDialog", "showAlertDialog" + System.identityHashCode(this))
        alertDialog = AlertDialog.Builder(this)
            .setTitle("Playback in Progress")
            .setMessage("Media is currently playing.")
            .setPositiveButton("OK", null)
            .create()
        alertDialog.show()
    }

    override fun onDestroy() {
        super.onDestroy()
        Log.i("onDestroy", "onDestroy" + System.identityHashCode(this))
        player.release() // Don't forget to release the player
    }
}
