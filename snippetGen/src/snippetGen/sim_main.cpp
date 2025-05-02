#include "Vtop.h" // Verilator generated header for the top module (using --top-module)
#include "verilated.h"
#include <cstdlib> // For getenv
#include <iostream>
#include <string> // For std::stoll

// Function to get simulation time limit from environment variable
vluint64_t get_sim_time_limit() {
  const char *time_limit_str = std::getenv("VERILATOR_SIM_TIME_LIMIT");
  if (time_limit_str) {
    try {
      long long limit = std::stoll(time_limit_str);
      if (limit > 0) {
        return static_cast<vluint64_t>(limit);
      } else {
        std::cerr << "Warning: Invalid VERILATOR_SIM_TIME_LIMIT value '"
                  << time_limit_str << "'. Using default." << std::endl;
      }
    } catch (const std::exception &e) {
      std::cerr << "Warning: Could not parse VERILATOR_SIM_TIME_LIMIT value '"
                << time_limit_str << "': " << e.what() << ". Using default."
                << std::endl;
    }
  }
  return 200; // Default simulation time limit (time units)
}

int main(int argc, char **argv) {
  VerilatedContext *contextp = new VerilatedContext;
  contextp->commandArgs(argc, argv);
  // Instantiate the Verilated module (using Vtop as the class name, mapped by
  // --top-module)
  Vtop *top = new Vtop{contextp};

  vluint64_t sim_time_limit = get_sim_time_limit();
  vluint64_t time = 0;

  std::cout << "Starting Verilator simulation (Max time: " << sim_time_limit
            << ")..." << std::endl;

  // Basic simulation loop - relies on the LLM-generated testbench for stimulus.
  // Provides a basic clock and reset sequence if the testbench doesn't drive
  // them. Ensure your Verilog top module has 'clk' and 'reset' inputs if using
  // this driver directly.
  top->clk = 0;
  top->reset = 1; // Assert reset initially

  while (!contextp->gotFinish() && time < sim_time_limit) {
    // Apply reset for the first few cycles (e.g., 10 time units)
    if (time >= 10) top->reset = 0; // De-assert reset
    // Toggle clock every time unit
    top->clk = !top->clk;

    // Evaluate model
    top->eval();

    // Increment time by 1 time unit
    contextp->timeInc(1);
    time++;

    // Optional: Add a small delay or yield if needed in complex simulations
    // Verilated::yield();
  }

  if (time >= sim_time_limit && !contextp->gotFinish()) {
    std::cout << "Warning: Simulation reached time limit (" << sim_time_limit
              << ") without $finish." << std::endl;
  } else {
    std::cout << "Verilator simulation finished via $finish at time " << time
              << std::endl;
  }

  top->final(); // Optional: Execute Verilog final blocks
  delete top;
  delete contextp;
  return 0;
}
