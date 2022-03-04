#!/bin/bash
if [ $# -eq 0 ]
	then
		#CMD=$(cat ~/dcmd)
		docker run --rm --net=host -it --shm-size=1024m cuplv/bounder bash
		#-c "java -jar $BOUNDER_JAR --mode expLoop"
	else
		DATADIR=$(realpath $1)
				echo "Data directory: $DATADIR"
				docker run -it --mount type=bind,source="$DATADIR",target=/home/bounder_host bounder bash

fi
