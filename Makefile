.PHONY: init
init:
	git clone https://github.com/verilator/verilator

.PHONY: clean
clean:
	rm -rf build obj_dir

.PHONY: build
build:
	docker build -t instrumented_verilator .

.PHONY: help
help:
	@echo "Usage: make init | make clean | make build"
	@echo "init: Clone the verilator repository"
	@echo "clean: Remove build and obj_dir directories"
	@echo "build: Build the Docker image for instrumented Verilator"
	@echo "all: Show this help message"

all: help