Running Unit Tests
==================
* Install Android Studio and SDK (level 26 and 29 are needed for unit tests) 
    - Make sure that `ANDROID_HOME` is set (e.g. `[user home]/Library/Android/sdk`)
* Install java 8 (I recommend using [JEnv](https://www.jenv.be/) and OpenJDK.  (As I recall this is currently a SOOT limitation)
* install z3 from here: https://github.com/Z3Prover/z3
    - when building, use `python3 scripts/mk_make.py --java` to compile the java bindings.
* set sbt heap size with `export SBT_OPTS="-Xmx2036M"`
* Run `sbt test`
* Note that some tests may take a while.
* It is recommended to develop in Intellij (community edition is fine)
* If using a non-default version of java and jenv, set the `JENV_VERSION` environment variable to the jenv version you want to use (e.g. `export JENV_VERSION=1.8`). You can list available versions using the command `jenv versions`.
* For jupyter notebooks, install nbdev hooks: https://nbdev.fast.ai/tutorials/git_friendly_jupyter.html
