#!/bin/bash
pg_dump -h localhost -U postgres postgres -p 3333 > ~/Desktop/15allDeref.sql
# note: use psql dbname < infile to restore
