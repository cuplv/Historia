#!/bin/bash
DATADIR=$(realpath $1)
echo "Data directory: $DATADIR"
docker run -it --mount type=bind,source="$DATADIR",target=/home/bounder_host bounder bash
