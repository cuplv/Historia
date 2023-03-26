#!/bin/bash
java -Xmx12G -jar $HOME/Documents/source/Bounder/soot_hopper/target/scala-2.13/soot_hopper-assembly-0.1.jar \
-m verify \
-c $PWD/config.json \
-b $HOME/Documents/data/historia_generalizability \
-u $PWD/nospec \
-o MEM --debug

