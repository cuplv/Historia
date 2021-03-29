#!/bin/bash
#docker pull postgres
PASS=$(sed 's/.*://' < ~/.pgpass)
docker run --name bounder-db -p 5433:5432 -e POSTGRES_PASSWORD=$PASS -d postgres 
