#!/bin/bash
#HOST=shme8881@plv1.colorado.edu
HOST=s@192.168.86.35
#HOST=ubuntu@198.59.7.90

#ssh -N -L 3333:localhost:5433 $HOST -p 80
ssh -N -L 3333:localhost:5433 $HOST
