all: run

.PHONY: init
init:
	if [ ! -d "verilator" ]; then \
		git clone https://github.com/verilator/verilator; \
	else \
		echo "verilator directory already exists. Skipping clone."; \
	fi

.PHONY: clean
clean:
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
