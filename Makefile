#TEST_FILES_DIR ?= transfuzzTestFiles
TEST_FILES_DIR ?= verismith

all: help

.PHONY: init
init:
	if [ ! -d "verilator" ]; then \
		git clone https://github.com/verilator/verilator; \
	else \
		echo "verilator directory already exists. Skipping clone."; \
	fi

.PHONY: clean
clean: cleanTransfuzzTestFiles cleanVerismith clearCoverage
	rm -rf build obj_dir

.PHONY: build
build: init
	docker build -t instrumentedverilator .

.PHONY: help
help:
	@echo "Instrumented Verilator Makefile"
	@echo ""
	@echo "Main targets:"
	@echo "  make all         - Default target (currently runs 'run')"
	@echo "  make init        - Clone the verilator repository if not exists"
	@echo "  make build       - Build the Docker image for instrumented Verilator"
	@echo "  make clean       - Remove build, obj_dir and clear coverage data"
	@echo "  make run         - Run the Docker container with testFiles mounted"
	@echo ""
	@echo "Coverage targets:"
	@echo "  make getCoverage       - Generate HTML coverage report from inside Docker"
	@echo "  make backupCoverage    - Backup current coverage reports to timestamped directory(by number of files executed)"
	@echo "  make dumpCoverage      - Get and backup coverage in one step"
	@echo "  make clearCoverage     - Remove all .dat coverage files"
	@echo "  make syncCoverage      - Continuously generate coverage until all tests are processed"
	@echo "  make plotCoverage      - Run script to plot coverage data"
	@echo "  make getCoverageCmd    - Print the gcovr command for coverage report generation"
	@echo "  make getFastCovCmd     - Print the fastcov command for faster coverage processing"
	@echo ""
	@echo "Cleanup targets:"
	@echo "  make cleanTransfuzzTestFiles  - Clean obj_dirs from transfuzzTestFiles"
	@echo "  make cleanVerismith           - Clean obj_dirs from verismith"
	@echo ""
	@echo "Utility targets:"
	@echo "  make server            - Start HTTP server on port 8080 for viewing reports"
	@echo "  make getExecOneFileCmd - Print command to execute a single Verilator file (usefull for running in the container(started by the make run command))"
	@echo ""
	@echo "Current test directory: $(TEST_FILES_DIR) (set with TEST_FILES_DIR=dirname) can be changed, it is usefull for the syncCoverage command to know what are the files that are intersting to look at"

.PHONY: run
run:
	docker run -it --rm -v $(PWD)/testFiles:/testFiles --workdir=/testFiles instrumentedverilator /bin/bash

.PHONY: getCoverage
getCoverage:
	docker exec -it $(shell docker ps -q --filter ancestor=instrumentedverilator) /bin/bash -c "gcovr --html --html-details -f '.*\.cpp$$' -e '(.*/)?(V3Coverage\.cpp|V3CoverageJoin\.cpp|V3EmitCMake\.cpp|V3EmitXml\.cpp|V3ExecGraph\.cpp|V3GraphTest\.cpp|V3HierBlock\.cpp|V3Trace\.cpp|V3TraceDecl\.cpp|V3EmitV\.cpp|V3TSP\.cpp|V3Scoreboard\.cpp|V3Stats\.cpp|V3ProtectLib\.cpp|V3Broken\.cpp|V3Interface\.cpp)$$' -o /testFiles/coverage_reports/coverage_report.html --root /verilator/src"

.PHONY: backupCoverage
backupCoverage:
	mv testFiles/coverage_reports coverage_reports.bak/$(shell printf "%03d" $$(find testFiles/$(TEST_FILES_DIR)/ -name 'obj_dir' -type d | wc -l))_files && mkdir testFiles/coverage_reports

.PHONY: dumpCoverage
dumpCoverage: getCoverage backupCoverage

.PHONY: cleanTransfuzzTestFiles
cleanTransfuzzTestFiles:
	rm -rf testFiles/transfuzzTestFiles/obj_dir_example_sim_*/obj_dir

.PHONY: cleanVerismith
cleanVerismith:
	rm -rf testFiles/verismith/obj_dir_example_sim_*/obj_dir

.PHONY: getCoverageCmd
getCoverageCmd:
	@echo "gcovr --html --html-details -f '.*\.cpp$$' -e '(.*/)?(V3Coverage\.cpp|V3CoverageJoin\.cpp|V3EmitCMake\.cpp|V3EmitXml\.cpp|V3ExecGraph\.cpp|V3GraphTest\.cpp|V3HierBlock\.cpp|V3Trace\.cpp|V3TraceDecl\.cpp)$' -o /testFiles/coverage_reports/coverage_report.html --root /verilator/src"

.PHONY: getFastCovCmd
getFastCovCmd:
	@echo "to be improved fastcov -o /testFiles/coverage_reports/coverage_report.json --include '.*\\.cpp$$' --exclude '(.*/)?(V3Coverage\\.cpp|V3CoverageJoin\\.cpp|V3EmitCMake\\.cpp|V3EmitXml\\.cpp|V3ExecGraph\\.cpp|V3GraphTest\\.cpp|V3HierBlock\\.cpp|V3Trace\\.cpp|V3TraceDecl\\.cpp)$$' --lcov --directory /verilator/src"

.PHONY: clearCoverage
clearCoverage:
	find . -name "*.dat" -type f -exec rm -f {} +

.PHONY: syncCoverage
syncCoverage: clearCoverage
	@while [ $$(find testFiles/$(TEST_FILES_DIR)/ -name 'obj_dir' -type d | wc -l) -lt $$(find testFiles/$(TEST_FILES_DIR) -type f -name 'top.sv' | wc -l) ]; do \
		make getCoverage; \
		make backupCoverage; \
	done
	make dumpCoverage

.PHONY: plotCoverage
plotCoverage:
	uv run testFiles/plotCoverage.py

.PHONY: server
server:
	uv run python3.13 -m http.server 8080

.PHONY: getExecOneFileCmd
getExecOneFileCmd:
	@echo '$$VERILATOR_ROOT/bin/verilator --cc --binary' -Wno-MULTIDRIVEN --Wno-UNOPTFLAT --Wno-NOLATCH --Wno-WIDTHTRUNC --Wno-CMPCONST --Wno-WIDTHEXPAND --Wno-UNSIGNED -CFLAGS "'-I/testFiles/include -I -g'" --threads 8 --comp-limit-blocks 10 file.sv