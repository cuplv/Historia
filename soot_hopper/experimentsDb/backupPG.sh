#!/bin/bash
pg_dump -h localhost -U postgres postgres -p 3333 > ~/Desktop/2AllDeref22.sql
# note: use psql dbname < infile to restore
