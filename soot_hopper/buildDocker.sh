#!/bin/bash
HASH=$(git rev-parse HEAD)
docker build --build-arg COMMITHASH="${HASH}"   -t bounder:100 .
