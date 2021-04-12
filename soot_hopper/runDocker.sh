#!/bin/bash
if [ $# -eq 0 ]
	then
		docker run -it bounder bash
	else
		DATADIR=$(realpath $1)
				echo "Data directory: $DATADIR"
				docker run -it --mount type=bind,source="$DATADIR",target=/home/bounder_host bounder bash

fi
