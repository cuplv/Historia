#!/bin/bash
cd /home/notebooks
jupyter lab --allow-root --NotebookApp.token='' --port=8888 --ip=0.0.0.0
