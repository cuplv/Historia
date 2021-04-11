#!/bin/bash
psql -h localhost -U postgres postgres -p 3333 -f setupPg.sql
