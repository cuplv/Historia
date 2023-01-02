Running Unit Tests
==================
* Install Android Studio and SDK (level 29 needed for unit tests) 
    - Make sure that `ANDROID_HOME` is set (e.g. `[user home]/Library/Android/sdk`)
* set sbt heap size with `export SBT_OPTS="-Xmx2036M"`
* Run `sbt test`
* Note that some tests may take a while.
* It is recommended to develop in Intellij (community edition is fine)
