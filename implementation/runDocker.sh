#!/bin/bash
if [ $# -eq 0 ]
	then
		docker run --rm  -it --shm-size=500m -v ~/.pgpass:/root/.pgpass -e BOUNDER_JAR='/home/bounder/target/scala-2.13/soot_hopper-assembly-0.1.jar' -p 3333:3333 cuplv/bounder bash -c 'java -jar $BOUNDER_JAR --mode expLoop'
		#-c "java -jar $BOUNDER_JAR --mode expLoop"
	else
		DATADIR=$(realpath $1)
				echo "Data directory: $DATADIR"
				docker run -it --mount type=bind,source="$DATADIR",target=/home/bounder_host bounder bash

fi
