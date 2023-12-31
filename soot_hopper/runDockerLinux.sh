#!/bin/bash
#BOUNDER_JAR="not this one!!!!"
if [ $# -eq 0 ] #--shm-size=4096m //TODO: shrinking this to save ram
	then
		#CMD=$(cat ~/dcmd)
		# to limit docker mem use -m 100G
		docker run  --rm --net=host -it --shm-size=500m -v ~/.pgpass:/root/.pgpass -e BOUNDER_JAR='/home/bounder/target/scala-2.13/soot_hopper-assembly-0.1.jar' cuplv/bounder bash -c 'java -jar $BOUNDER_JAR --mode expLoop'
		#docker run --rm --net=host --shm-size=4096m -v ~/.pgpass:/root/.pgpass -e BOUNDER_JAR='/home/bounder/target/scala-2.13/soot_hopper-assembly-0.1.jar' cuplv/bounder bash -c 'java -jar $BOUNDER_JAR --mode expLoop'
	else
		DATADIR=$(realpath $1)
				echo "Data directory: $DATADIR"
				docker run -it --mount type=bind,source="$DATADIR",target=/home/bounder_host bounder bash

fi
