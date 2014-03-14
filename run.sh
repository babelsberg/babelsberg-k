#!/usr/bin/env bash

which krun 2>&1 >/dev/null
if [ $? -ne 0 ]; then
    echo "Please put krun in your PATH"
    exit 1
fi

which ruby 2>&1 >/dev/null
if [ $? -ne 0 ]; then
    echo "Please put ruby in your PATH"
    exit 1
fi

if [ ! -e "babelsberg-int-kompiled" ]; then
    which kcompile 2>&1 >/dev/null
    if [ $? -ne 0 ]; then
	echo "Please put kcompile in your PATH"
	exit 1
    fi
    kcompile babelsberg-int.k
fi

if [ "$1" == "" ]; then
    file="./example.int"
else
    file="$1"
fi
echo "Running $file"
cat "$file"
sleep 3
krun "$file" &
sleep 2
ruby ./cassowary-gateway.rb
sleep 1
