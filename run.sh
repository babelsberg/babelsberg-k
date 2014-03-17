#!/usr/bin/env bash

if [ $# -lt 2 ]; then
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

if [ $semantics -nt $compiledS ]; then
    echo "Need to recompile..."
    rm --one-file-system -rf babelsberg-*-kompiled
    # K doesn't like multiple compiled things around
    which kompile 2>&1 >/dev/null
    if [ $? -ne 0 ]; then
	echo "Please put kompile in your PATH"
	exit 1
    fi
    kompile $semantics
    if [ $? -ne 0 ]; then
	exit 1
    fi
fi

echo "Running $program"
cat "$program"
krun "$program" &
export krun="$!"

function cleanup() {
    pkill -9 -P $krun
    kill -9 $krun
}
trap cleanup SIGINT

sleep 2
ruby ./cassowary-gateway.rb
sleep 1
