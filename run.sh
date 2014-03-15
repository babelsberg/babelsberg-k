#!/usr/bin/env bash

if [ $# -ne 2 ]; then
    echo "./run.sh babelsberg-SEMANTICS.k program"
    exit 1
fi

semantics=$1
compiledS=${semantics%%.*}-kompiled
program=$2

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

if [ ! -e $compiledS ]; then
    rm --one-file-system -rf babelsberg-*-kompiled
    # K doesn't like multiple compiled things around
    which kompile 2>&1 >/dev/null
    if [ $? -ne 0 ]; then
	echo "Please put kompile in your PATH"
	exit 1
    fi
    kompile $semantics || exit 1
fi

echo "Running $program"
cat "$program"
krun "$program" &
krun="$!"
sleep 2
ruby ./cassowary-gateway.rb
sleep 1
kill -9 $krun
