#TEST_FILES_DIR ?= transfuzzTestFiles
TEST_FILES_DIR ?= verismith

all: run

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
	@echo "Usage: make init | make clean | make build"
	@echo "init: Clone the verilator repository"
	@echo "clean: Remove build and obj_dir directories"
	@echo "build: Build the Docker image for instrumented Verilator"
	@echo "all: Show this help message"

.PHONY: run
run:
	docker run -it --rm -v $(PWD)/testFiles:/testFiles --workdir=/testFiles instrumentedverilator /bin/bash

.PHONY: getCoverage
getCoverage:
	docker exec -it $(shell docker ps -q --filter ancestor=instrumentedverilator) /bin/bash -c "gcovr --html --html-details -f '.*\.cpp$$' -e '(.*/)?(V3Coverage\.cpp|V3CoverageJoin\.cpp|V3EmitCMake\.cpp|V3EmitXml\.cpp|V3ExecGraph\.cpp|V3GraphTest\.cpp|V3HierBlock\.cpp|V3Trace\.cpp|V3TraceDecl\.cpp)$$' -o /testFiles/coverage_reports/coverage_report.html --root /verilator/src"

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