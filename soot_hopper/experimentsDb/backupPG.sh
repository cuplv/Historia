#!/bin/bash
pg_dump -h localhost -U postgres postgres -p 3333 > ~/Desktop/55select/apr-6-2022.sql
# note: use psql dbname < infile to restore
