#!/bin/bash
java -Xmx12G -jar $HOME/Documents/source/Bounder/soot_hopper/target/scala-2.13/soot_hopper-assembly-0.1.jar \
-m verify -c /home/s/Documents/source/bounder/notebooks/ossExp/SpecGen/com.nutomic.syncthingandroid/SensitiveDerefCallinCaused/0/config_spec_locreach.json -b /home/s/Documents/data/historia_generalizability -u /home/s/Documents/source/bounder/notebooks/ossExp/SpecGen/com.nutomic.syncthingandroid/SensitiveDerefCallinCaused/0/locreach -o MEM --debug
