#!/bin/bash
#psql -h localhost -U postgres postgres -p 3333 -f setupPg.sql
psql -h localhost -U postgres postgres -p 5432 -f setupPg.sql
