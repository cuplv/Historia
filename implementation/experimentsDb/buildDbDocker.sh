#!/bin/bash
HASH=$(git rev-parse HEAD)
docker build --build-arg COMMITHASH="${HASH}" -t historia_postgres .
