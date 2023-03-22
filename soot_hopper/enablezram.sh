#!/bin/bash
# run with sudo
echo 0 > /sys/module/zswap/parameters/enabled
modprobe zram
echo 100G > /sys/block/zram0/disksize
mkswap --label zram0 /dev/zram0
swapon -p 600 /dev/zram0
