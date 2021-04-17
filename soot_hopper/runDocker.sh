#!/bin/bash
if [ $# -eq 0 ]
	then
		docker run -it bounder:100 bash 
		#-c "java -jar $BOUNDER_JAR --mode expLoop"
	else
		DATADIR=$(realpath $1)
				echo "Data directory: $DATADIR"
				docker run -it --mount type=bind,source="$DATADIR",target=/home/bounder_host bounder bash

fi
