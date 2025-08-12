#!/bin/bash
$VERILATOR_ROOT/bin/verilator --cc --binary -Wno-MULTIDRIVEN --Wno-UNOPTFLAT --Wno-NOLATCH --Wno-WIDTHTRUNC --Wno-CMPCONST --Wno-WIDTHEXPAND --Wno-UNSIGNED --Wno-MULTITOP -CFLAGS "-I/testFiles/include -I -g" --threads 8 --comp-limit-blocks 10 $1
fastcov -o report.info -b -d /verilator/src --lcov --exclude-glob "*.[hly]" --include .cpp --exclude /usr/include V3Coverage.cpp V3CoverageJoin.cpp V3EmitCMake.cpp V3EmitXml.cpp V3ExecGraph.cpp V3GraphTest.cpp V3HierBlock.cppV3Trace.cpp V3TraceDecl.cpp V3EmitV.cpp V3TSP.cpp V3Scoreboard.cpp V3Stats.cpp V3ProtectLib.cpp V3Broken.cpp V3Interface.cpp
_tt=$(genhtml -o /testFiles/coverage_reports report.info | tail -n 2 | grep -oP '\b\d+\.\d(?=\%)')
echo $_tt >> naive.csv

