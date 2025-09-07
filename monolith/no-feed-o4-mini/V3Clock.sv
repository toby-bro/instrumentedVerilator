class MyCounter;
  bit [3:0] cnt;
  function new(); cnt = 0; endfunction
  function void inc(); cnt = cnt + 1; endfunction
  function bit [3:0] get(); return cnt; endfunction
endclass
module ConvertWriteRefsToReadSV(input  logic [7:0] in_bus,
                                 output logic [7:0] out_bus);
  assign out_bus = ~in_bus;
endmodule
module ClockEdgeSense(input  logic clk,
                      input  logic reset_n,
                      input  logic data,
                      output logic q,
                      output logic p);
  always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      q <= 1'b0;
      p <= 1'b0;
    end else begin
      if (data) begin
        q <= ~q;
      end else begin
        q <= q;
      end
      p <= q;
    end
  end
endmodule
module CoverToggle(input  logic        clk,
                   input  logic        orig,
                   input  logic        change_in,
                   output logic [7:0]  inc,
                   output logic        change_out);
  always @(posedge clk) begin
    if (orig ^ change_in) begin
      inc <= inc + 1;
      change_out <= orig;
    end else if (orig != change_in) begin
      inc <= inc - 1;
      change_out <= change_in;
    end else begin
      change_out <= change_in;
    end
  end
endmodule
module SenseEquationCombine(input  logic [3:0] bus,
                            output logic       sens_eq);
  assign sens_eq = bus[0] | bus[1] | bus[2] | bus[3];
endmodule
module ExecGraphLoop(input  logic [1:0] sel,
                     input  logic [7:0] data_in,
                     output logic [7:0] data_out);
  integer i;
  always @(sel or data_in) begin
    data_out = data_in;
    for (i = 0; i < 4; i = i + 1) begin
      if (sel == i) data_out = data_out + i;
    end
  end
endmodule
module VarScopeSample(input  logic clk,
                      input  logic in_sig,
                      output logic out_sig);
  logic sampled;
  always @(posedge clk) begin
    sampled   <= in_sig;
    out_sig   <= sampled;
  end
endmodule
module ClassProc(input  logic        clk,
                 input  logic        enable,
                 output logic [3:0]  count_out);
  MyCounter c;
  always @(posedge clk) begin
    c = new();
    if (enable) c.inc();
    count_out <= c.get();
  end
endmodule
module ParamGen #(parameter N = 4)
                 (input  logic [N-1:0] in,
                  output logic [N-1:0] out);
  genvar gi;
  generate
    for (gi = 0; gi < N; gi = gi + 1) begin : genblk
      assign out[gi] = in[gi] ^ in[N-1-gi];
    end
  endgenerate
endmodule
