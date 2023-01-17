#!/bin/bash
echo "" > ./containers
./runDockerLinux.sh >> ./containers & #1
./runDockerLinux.sh >> ./containers & #2
./runDockerLinux.sh >> ./containers & #3
./runDockerLinux.sh >> ./containers & #4
./runDockerLinux.sh >> ./containers & #5
./runDockerLinux.sh >> ./containers & #6

