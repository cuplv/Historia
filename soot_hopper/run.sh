#!/bin/bash
java -Xmx12G -jar /home/cc/Documents/source/Bounder/soot_hopper/target/scala-2.13/soot_hopper-assembly-0.1.jar -m \
verify \
-c \
/home/cc/Documents/source/bounder/notebooks/ossExp/SpecGen/de.danoeh.antennapod/SensitiveDerefCallinCaused/0/config_spec.json \
-b \
$HOME/Documents/data/historia_generalizability \
-u \
/home/cc/Documents/source/bounder/notebooks/ossExp/SpecGen/de.danoeh.antennapod/SensitiveDerefCallinCaused/0/spec \
-o \
MEM \
--debug
