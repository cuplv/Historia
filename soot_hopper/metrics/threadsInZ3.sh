#!/bin/bash
jstack $1 |grep "com.microsoft.z3.Native.INTERNALsolverCheck" |wc -l
