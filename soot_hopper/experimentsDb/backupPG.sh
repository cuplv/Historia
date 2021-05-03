#!/bin/bash
pg_dump -h localhost -U postgres postgres -p 3333 > ~/Desktop/2AllDeref4_29_2021_suspected_missing.sql
# note: use psql dbname < infile to restore
