#!/bin/bash

echo "************************************************************************"
echo "************************************************************************"
echo "************************************************************************"
echo ""
echo ""
echo "start make"
echo ""
echo ""
echo "************************************************************************"
echo "************************************************************************"
echo "************************************************************************"

rm -rf build/

make clean

RVHOME=/opt/riscv64
JREPATH=/home/zifeihan/jre/jre19

bash configure \
--openjdk-target=riscv64-unknown-linux-gnu \
--disable-warnings-as-errors \
--with-sysroot=${RVHOME}/sysroot \
--with-boot-jdk=${JREPATH} \
--with-jvm-variants=server \
--with-native-debug-symbols=internal \
--with-debug-level=fastdebug

make all

/home/zifeihan/rvv/qemu-7.1.0-rc4-riscv64/bin/qemu-riscv64 -cpu rv64,v=true,vlen=256,vext_spec=v1.0 -L /opt/riscv64/sysroot ./java -version