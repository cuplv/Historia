#!/bin/bash
if [ -z $1 ]
then
	echo "Output file needed."
else
	docker save -o $1 cuplv/bounder
fi
