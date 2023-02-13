#!/bin/bash
pg_dump -h localhost -U postgres postgres -p 5433 > ~/Desktop/feb-12-2023.sql
# note: use psql dbname < infile to restore

# note2: for version mismatch between pg server and client:
#sudo sh -c 'echo "deb http://apt.postgresql.org/pub/repos/apt/ `lsb_release -cs`-pgdg main" >> /etc/apt/sources.list.d/pgdg.list'
#wget --quiet -O - https://www.postgresql.org/media/keys/ACCC4CF8.asc | sudo apt-key add -
#sudo apt-get update
#sudo apt-get install -y postgresql-client-11
