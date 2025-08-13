timeunit 1ns;
timeprecision 1ps;
package util_pkg;
   class Holder;
      rand int value;
      function new(int v);
         value = v;
      endfunction
   endclass
endpackage
module dpi_sample (
   input  logic         clk,
   input  logic  [31:0] in_data,
   output logic  [31:0] out_data
);
   import "DPI-C" function int c_inc (input int a);
   task automatic sv_alert (input int v);
   endtask
   export "DPI-C" task sv_alert;
   function int sv_add (input int a, input int b);
      sv_add = a + b;
   endfunction
   export "DPI-C" function sv_add;
   logic [31:0] acc = 32'd0;
   always_ff @(posedge clk) begin
      acc <= c_inc(acc ^ in_data);
      sv_alert(acc);
   end
   assign out_data = acc;
endmodule
module class_cov #(
   parameter int WIDTH = 8
) (
   input  logic               clk,
   input  logic [WIDTH-1:0]   in_bus,
   output logic               hit
);
   import util_pkg::*;
   Holder h;
   always_ff @(posedge clk) begin
      h = new(in_bus);
      cover (h.value == in_bus);
      hit <= (h.value == in_bus);
   end
endmodule
module array_public (
   input  logic i,
   output logic o
);
   (* public_flat_rd *) logic [3:0] pub_array [0:1][0:7];
   always_comb begin
      pub_array[0][0] = 4'hA;
      o = pub_array[0][0][0] ^ i;
   end
endmodule
module event_mod (
   input  logic clk,
   output logic flag
);
   event e;
   always_ff @(posedge clk) begin
      -> e;
      flag <= 1'b1;
   end
endmodule
module time_param_mod #(
   parameter string ID = "TPM"
) (
   input  logic in_sig,
   output logic out_sig
);
   timeunit 100ps;
   timeprecision 1ps;
   assign out_sig = in_sig;
endmodule
