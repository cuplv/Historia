Historia Overview
=================
Historia is a static analysis tool for event-driven applciations.  Specificially, this tool addresses the pproblem of analyzing an Android application absent of the specific implementation of the framework.  In order to capture the behavior of the framework, Historia uses a domain specific language called Callback Control Flow Temporal Logic (CBCFTL for short). The full paper with details behind the theory may be found [here](https://doi.org/10.1145/3622865).

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


A step by step guide on using Historia
======================================
This guide may be found in the jupyter notebook: https://github.com/cuplv/Historia/blob/master/notebooks/HistoriaExampleAndExplanation.ipynb
