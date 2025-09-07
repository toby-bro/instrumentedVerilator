module ff_module(input logic clk, input logic rst, input logic [3:0] d, output logic [3:0] q);
always_ff @(posedge clk or negedge rst) begin
  if (!rst) q <= 4'b0000;
  else q <= d;
end
endmodule
module comb_module(input logic a, input logic b, input logic c, output logic y);
logic temp;
always_comb begin
  if (a & b)
    temp = c;
  else
    temp = ~c;
  y = temp ^ a;
end
endmodule
module latch_module(input logic en, input logic d, output logic q);
always_latch begin
  if (en)
    q = d;
end
endmodule
module edge_level_module(input logic clk, input logic in_sig, output logic out_sig);
always @(posedge clk or in_sig) begin
  if (in_sig)
    out_sig = 1'b1;
  else
    out_sig = 1'b0;
end
endmodule
module wildcard_module(input logic [1:0] s, input logic in0, input logic in1, output logic out);
always @* begin
  out = s ? in1 : in0;
end
endmodule
module continuous_assign_module(input logic a, input logic b, output logic c);
assign c = a & b;
endmodule
module fork_module(input logic clk, input logic en, input logic [1:0] d, output logic [1:0] q1, output logic [1:0] q2);
always_ff @(posedge clk) begin
  if (en) begin
    fork
      begin q1 <= d; end
      begin q2 <= d + 1; end
    join
  end
end
endmodule
module case_module(input logic [2:0] sel, input logic [7:0] in_bus, output logic [7:0] out_bus);
always_comb begin
  case (sel)
    3'b000: out_bus = in_bus;
    3'b001: out_bus = in_bus << 1;
    default: out_bus = in_bus >> 1;
  endcase
end
endmodule
module event_module(input logic clk, input logic in_sig, output logic out_sig);
event trigger_event;
always_ff @(posedge clk) begin
  if (in_sig)
    -> trigger_event;
end
always @(trigger_event or in_sig) begin
  out_sig = in_sig;
end
endmodule
module legacy_always_module(input logic clk, input logic in1, output reg out1);
always @(posedge clk) begin
  out1 = in1;
end
endmodule
