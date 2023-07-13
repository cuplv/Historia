#!/bin/bash
HASH=$(git rev-parse HEAD)
docker build --no-cache --build-arg COMMITHASH="${HASH}" -t historia_postgres .
