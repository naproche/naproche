#!/usr/bin/env bash

while read -r rev; do
    git checkout "$rev" 2> /dev/null
    echo "$rev"
    stack build &> /dev/null
    start=`date +%s.%N`
    stack test &> /dev/null
    end=`date +%s.%N`
    echo "$(echo "$end - $start" | bc -l)"
    echo ""
done < <(git rev-list "$1")
