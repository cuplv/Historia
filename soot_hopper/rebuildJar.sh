#!/bin/bash
rm target/scala-2.13/soot_hopper-assembly-0.1.jar 2>/dev/null
sbt assembly
