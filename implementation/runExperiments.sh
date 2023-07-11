#!/bin/bash
sbt clean
sbt -J-Xmx16G "testOnly edu.colorado.plv.bounder.symbolicexecutor.Experiments"
