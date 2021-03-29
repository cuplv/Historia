#!/bin/bash
#docker pull postgres
docker run --name bounder-db -e POSTGRES_PASSWORD=$(cat ~/.pgpass) -e POSTGRES_USER="bounder" -d postgres
