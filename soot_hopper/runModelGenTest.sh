#!/bin/bash
echo "out file: testOut.txt"
sbt clean;sbt -J-Xmx60G "testOnly edu.colorado.plv.bounder.synthesis.EnumModelGeneratorTest" 2> testErr.txt 1>testOut.txt
