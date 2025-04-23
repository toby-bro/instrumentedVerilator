#TEST_FILES_DIR ?= transfuzzTestFiles
TEST_FILES_DIR ?= verismith

all: help

.PHONY: init
init:
	git submodule init
	git submodule update --recursive

.PHONY: clean
clean: cleanTransfuzzTestFiles cleanVerismith clearCoverage
	rm -rf build obj_dir

.PHONY: build
build: init build-verilator build-yosys

.PHONY: build-verilator
build-verilator: init
	docker build -t instrumentedverilator .

.PHONY: build-yosys
build-yosys: init
	docker build -t instrumentedyosys -f Dockerfile.yosys .

.PHONY: help
help:
	@echo "Instrumented Verilator/Yosys Makefile"
	@echo ""
	@echo "Main targets:"
	@echo "  make all              - Default target (currently runs 'run')"
	@echo "  make init             - Clone the verilator repository if not exists"
	@echo "  make build-verilator  - Build the Docker image for instrumented Verilator"
	@echo "  make build-yosys      - Build the Docker image for instrumented Yosys"
	@echo "  make clean            - Remove build, obj_dir and clear coverage data"
	@echo "  make run              - Run the Docker container with testFiles mounted (Verilator)"
	@echo "  make run-yosys        - Run the Docker container with testFiles mounted (Yosys)"
	@echo ""
	@echo "Coverage targets:"
	@echo "  make getCoverage       - Generate HTML coverage report from inside Docker (Verilator)"
	@echo "  make getYosysCoverage  - Generate HTML coverage report for Yosys"
	@echo "  make backupCoverage    - Backup current coverage reports (Verilator)"
	@echo "  make backupYosysCoverage - Backup current coverage reports (Yosys)"
	@echo "  make dumpCoverage      - Get and backup coverage in one step (Verilator)"
	@echo "  make dumpYosysCoverage - Get and backup coverage in one step (Yosys)"
	@echo "  make clearCoverage     - Remove all .dat coverage files for both tools"
	@echo "  make syncCoverage      - Continuously generate coverage until all tests are processed (Verilator)"
	@echo "  make syncYosysCoverage - Continuously generate coverage until all tests are processed (Yosys)"
	@echo "  make plotCoverage      - Run script to plot coverage data"
	@echo "  make getCoverageCmd    - Print the gcovr command for coverage report generation (Verilator)"
	@echo "  make getYosysCoverageCmd - Print the gcovr command for Yosys coverage"
	@echo ""
	@echo "Cleanup targets:"
	@echo "  make cleanTransfuzzTestFiles  - Clean obj_dirs from transfuzzTestFiles"
	@echo "  make cleanVerismith           - Clean obj_dirs from verismith"
	@echo ""
	@echo "Utility targets:"
	@echo "  make server            - Start HTTP server on port 8080 for viewing reports"
	@echo "  make getExecOneFileCmd - Print command to execute a single Verilator file"
	@echo "  make getExecYosysFileCmd - Print command to execute a single Yosys file"
	@echo ""
	@echo "Current test directory: $(TEST_FILES_DIR) (set with TEST_FILES_DIR=dirname)"

.PHONY: run
run:
	docker run -it --rm -v $(PWD)/testFiles:/testFiles --workdir=/testFiles instrumentedverilator /bin/bash

.PHONY: run-yosys
run-yosys:
	docker run -it --rm -v $(PWD)/testFiles:/testFiles --workdir=/testFiles instrumentedyosys /bin/bash

.PHONY: getCoverage
getCoverage:
	docker exec -it $(shell docker ps -q --filter ancestor=instrumentedverilator) /bin/bash -c "gcovr --html --html-details -f '.*\.cpp$$' -e '(.*/)?(V3Coverage\.cpp|V3CoverageJoin\.cpp|V3EmitCMake\.cpp|V3EmitXml\.cpp|V3ExecGraph\.cpp|V3GraphTest\.cpp|V3HierBlock\.cpp|V3Trace\.cpp|V3TraceDecl\.cpp|V3EmitV\.cpp|V3TSP\.cpp|V3Scoreboard\.cpp|V3Stats\.cpp|V3ProtectLib\.cpp|V3Broken\.cpp|V3Interface\.cpp)$$' -o /testFiles/coverage_reports/coverage_report.html --root /verilator/src"

.PHONY: getYosysCoverage
getYosysCoverage:
	docker exec -it $(shell docker ps -q --filter ancestor=instrumentedyosys) /bin/bash -c "gcovr --html --html-details -f '.*\.(cc|cpp)$$' -o /testFiles/yosys_coverage_reports/coverage_report.html --root /yosys"

.PHONY: backupCoverage
backupCoverage:
	mv testFiles/coverage_reports coverage_reports.bak/$(shell printf "%03d" $$(find testFiles/$(TEST_FILES_DIR)/ -name 'obj_dir' -type d | wc -l))_files && mkdir testFiles/coverage_reports

.PHONY: backupYosysCoverage
backupYosysCoverage:
	mv testFiles/yosys_coverage_reports yosys_coverage_reports.bak/$(shell printf "%03d" $$(find testFiles/$(TEST_FILES_DIR)/ -name 'synth_out' -type d | wc -l))_files && mkdir testFiles/yosys_coverage_reports

.PHONY: dumpCoverage
dumpCoverage: getCoverage backupCoverage

.PHONY: dumpYosysCoverage
dumpYosysCoverage: getYosysCoverage backupYosysCoverage

.PHONY: cleanTransfuzzTestFiles
cleanTransfuzzTestFiles:
	rm -rf testFiles/transfuzzTestFiles/obj_dir_example_sim_*/obj_dir

.PHONY: cleanVerismith
cleanVerismith:
	rm -rf testFiles/verismith/obj_dir_example_sim_*/obj_dir

.PHONY: getCoverageCmd
getCoverageCmd:
	@echo "gcovr --html --html-details -f '.*\.cpp$$' -e '(.*/)?(V3Coverage\.cpp|V3CoverageJoin\.cpp|V3EmitCMake\.cpp|V3EmitXml\.cpp|V3ExecGraph\.cpp|V3GraphTest\.cpp|V3HierBlock\.cpp|V3Trace\.cpp|V3TraceDecl\.cpp)$' -o /testFiles/coverage_reports/coverage_report.html --root /verilator/src"

.PHONY: getYosysCoverageCmd
getYosysCoverageCmd:
	@echo "gcovr --html --html-details -f '.*\.(cc|cpp)$$' -o /testFiles/yosys_coverage_reports/coverage_report.html --root /yosys"

.PHONY: getFastCovCmd
getFastCovCmd:
	@echo "to be improved fastcov -o /testFiles/coverage_reports/coverage_report.json --include '.*\\.cpp$$' --exclude '(.*/)?(V3Coverage\\.cpp|V3CoverageJoin\\.cpp|V3EmitCMake\\.cpp|V3EmitXml\\.cpp|V3ExecGraph\\.cpp|V3GraphTest\\.cpp|V3HierBlock\\.cpp|V3Trace\\.cpp|V3TraceDecl\\.cpp)$$' --lcov --directory /verilator/src"

.PHONY: clearCoverage
clearCoverage:
	find . -name "*.gcda" -type f -exec rm -f {} +
	find . -name "*.gcno" -type f -exec rm -f {} +
	find . -name "*.dat" -type f -exec rm -f {} +

.PHONY: syncCoverage
syncCoverage: clearCoverage
	@while [ $$(find testFiles/$(TEST_FILES_DIR)/ -name 'obj_dir' -type d | wc -l) -lt $$(find testFiles/$(TEST_FILES_DIR) -type f -name 'top.sv' | wc -l) ]; do \
		make getCoverage; \
		make backupCoverage; \
	done
	make dumpCoverage

.PHONY: syncYosysCoverage
syncYosysCoverage: clearCoverage
	@while [ $$(find testFiles/$(TEST_FILES_DIR)/ -name 'synth_out' -type d | wc -l) -lt $$(find testFiles/$(TEST_FILES_DIR) -type f -name 'top.sv' | wc -l) ]; do \
		make getYosysCoverage; \
		make backupYosysCoverage; \
	done
	make dumpYosysCoverage

.PHONY: plotCoverage
plotCoverage:
	uv run testFiles/plotCoverage.py

.PHONY: server
server:
	uv run python3.13 -m http.server 8080

.PHONY: getExecOneFileCmd
getExecOneFileCmd:
	@echo '$$VERILATOR_ROOT/bin/verilator --cc --binary' -Wno-MULTIDRIVEN --Wno-UNOPTFLAT --Wno-NOLATCH --Wno-WIDTHTRUNC --Wno-CMPCONST --Wno-WIDTHEXPAND --Wno-UNSIGNED -CFLAGS "'-I/testFiles/include -I -g'" --threads 8 --comp-limit-blocks 10 file.sv

.PHONY: getExecYosysFileCmd
getExecYosysFileCmd:
	@echo 'yosys -p "read_verilog file.sv; synth -top top; write_verilog /testFiles/synth_out/synth.v"'
