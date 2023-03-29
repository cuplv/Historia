#!/bin/bash
DYLD_LIBRARY_PATH=/Users/shawnmeier/software/z3/build java -Xmx12G -jar $HOME/Documents/source/Bounder/soot_hopper/target/scala-2.13/soot_hopper-assembly-0.1.jar \
-m verify \
-c $PWD/config_spec_locreach.json \
-b $HOME/Documents/data/historia_generalizability \
-u $PWD/locreach \
-o MEM --debug

