# Instrumented Verilator

This repository provides a Docker-based setup for an instrumented version of [Verilator](https://github.com/verilator/verilator), the open-source Verilog/SystemVerilog simulator and compiler. The primary purpose is to analyze code coverage of Verilator's internal components when processing different Verilog/SystemVerilog inputs.

## Purpose

- Generate code coverage metrics for Verilator's internal C++ implementation
- Identify areas of Verilator's codebase that aren't thoroughly exercised by test files
- Visualize coverage data to track improvements over time

## Getting Started

### Prerequisites

- Docker
- Make
- Python3 (with uv package manager (for visualization) makes everything easier)

### Setup and Usage

1. Clone this repository
2. Initialize the Verilator submodule: `make init`
3. Build the Docker image: `make build`
4. Run the Docker container: `make run`

Once inside the container, you can execute Verilog test files and collect coverage data. Use `make getExecOneFileCmd` to see the command format for running individual files.

## Coverage Analysis Workflow

1. Place test files in `testFiles/verismith` or `testFiles/transfuzzTestFiles`
2. Use `make syncCoverage` to automatically run tests and collect coverage data
3. View coverage reports in `coverage_reports.bak/` folders
4. Visualize coverage trends with `make plotCoverage`
5. Browse reports in a web browser using `make server`

## Key Features

- Instrumented Verilator build with gcov support
- Automatic test execution and coverage collection
- Coverage data visualization tools
- Support for multiple test sources (verismith, transfuzz)
- Docker-based environment for consistent results

## Available Commands

The Makefile provides numerous commands for managing the workflow. Use `make help` to see all available options.

## Directory Structure

- `verilator/`: Verilator source code (added via `make init`)
- `testFiles/`: Test Verilog/SystemVerilog files
- `coverage_reports.bak/`: Archived coverage reports
- `testFiles/plotCoverage.py`: Script for visualizing coverage data

## Acknowledgments

Thank you Frank for the initial project code.
