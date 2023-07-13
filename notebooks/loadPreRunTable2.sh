#!/bin/bash
psql -h localhost -U postgres postgres -p 5432 < /home/table2results/table2_historia.sql
