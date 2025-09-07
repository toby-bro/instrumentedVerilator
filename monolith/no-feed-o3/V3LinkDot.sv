package pkg_types;
  typedef enum logic [1:0] {IDLE, RUN, STOP} state_t;
  function automatic state_t next_state (input state_t in);
    next_state = state_t'(in);
  endfunction
endpackage
package pkg_classes;
  class base_c #(parameter int W = 8);
    pure virtual function void doit (input logic [W-1:0] data);
  endclass
  class derived_c #(parameter int W = 8) extends base_c #(W);
    function new ();
      super.new();
    endfunction
    virtual function void doit (input logic [W-1:0] data);
    endfunction
  endclass
endpackage
interface bus_if #(parameter WIDTH = 8) (input logic clk);
  logic [WIDTH-1:0] data;
  modport master (input  clk, output data);
  modport slave  (input  clk, input  data);
endinterface
module if_master (
  input  logic               clk,
  input  logic [7:0]         din,
  bus_if.master              ifc,
  output logic [7:0]         dout
);
  assign ifc.data = din;
  assign dout     = din;
endmodule
module if_slave (
  input  logic          clk,
  bus_if.slave          ifc,
  output logic [7:0]    dout
);
  assign dout = ifc.data;
endmodule
module system_mod (
  input  logic        clk,
  input  logic [7:0]  in_data,
  output logic [7:0]  out_data
);
  bus_if #(8) bus (clk);
  logic [7:0] mid;
  if_master m (
    .clk (clk),
    .din (in_data),
    .ifc (bus),
    .dout(mid)
  );
  if_slave s (
    .clk (clk),
    .ifc (bus),
    .dout(out_data)
  );
endmodule
module enum_user (
  input  logic [1:0] in_state,
  output pkg_types::state_t out_state
);
  import pkg_types::*;
  assign out_state = next_state(state_t'(in_state));
endmodule
module class_mod #(
  parameter int W = 8
)(
  input  logic [W-1:0] din,
  output logic [W-1:0] dout
);
  import pkg_classes::*;
  derived_c #(W) obj = new();
  assign dout = din;
endmodule
module clkblk_mod (
  input  logic clk,
  input  logic d,
  output logic q
);
  logic dummy;
  always_ff @(posedge clk) q <= d;
  clocking cb @(posedge clk);
    output dummy;
  endclocking
endmodule
module genblk_mod (
  input  logic in_bit,
  output logic out_bit
);
  generate
    if (1) begin
      logic temp;
      assign temp  = in_bit;
      assign out_bit = temp;
    end
  endgenerate
endmodule
