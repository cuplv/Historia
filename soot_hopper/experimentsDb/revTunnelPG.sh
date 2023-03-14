#!/bin/bash
# allow remote workers to connect to local machine
#HOST=shme8881@plv1.colorado.edu
HOST=cc@129.114.109.38
#HOST=ubuntu@198.59.7.90
#HOST=s@192.168.86.161

#ssh -N -L 3333:localhost:5433 $HOST -p 80
ssh -R 5433:localhost:5433 $HOST
