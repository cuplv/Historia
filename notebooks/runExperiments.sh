#!/bin/bash
sbt clean
cd ../bounder
sbt -J-Xmx16G "testOnly edu.colorado.plv.bounder.symbolicexecutor.Experiments"
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
cat "${SCRIPT_DIR}/log/logging.log" |grep "Row " |sed "s/ERROR/RESULT/"
