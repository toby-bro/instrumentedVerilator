#!/bin/bash
echo '' > testFiles/naive.csv

for i in {51..100};
    do _tt=$(docker run -it --rm -v $(pwd)/naive:/naive -v $(pwd)/testFiles:/testFiles -v $(pwd)/snippetGen:/snippetGen --workdir=/testFiles ghcr.io/toby-bro/instrumentedverilator:main ./dumping.sh /naive/$i.sv)
done
