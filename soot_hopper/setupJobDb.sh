#!/bin/bash
#docker pull postgres
docker run -name bounder-db -e POSTGRES_PASSWORD=$(cat ~/.ssh/postgres-password) -d postgres
