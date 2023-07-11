#!/bin/bash
time java -Xmx150G -jar $HOME/Documents/source/Bounder/soot_hopper/target/scala-2.13/soot_hopper-assembly-0.1.jar \
-m info \
-c $PWD/config_spec.json \
-b $HOME/Documents/data/historia_generalizability \
-u $PWD/spec \
-o DB --debug

