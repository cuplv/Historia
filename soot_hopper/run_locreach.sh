#!/bin/bash
time java -Xmx12G -jar $HOME/Documents/source/Bounder/soot_hopper/target/scala-2.13/soot_hopper-assembly-0.1.jar \
-m verify \
-c $PWD/config_spec_locreach.json \
-b $HOME/Documents/data/historia_generalizability \
-u $PWD/locreach \
-o MEM --debug

