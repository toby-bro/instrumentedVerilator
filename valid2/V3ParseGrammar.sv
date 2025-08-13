class dummy_c;
   int m;
   function new();
      m = 0;
   endfunction
endclass
module supply_ranges (
   input  logic in1,
   output logic out1
);
   supply0 gnd;
   supply1 vdd;
   logic [7:0]           packedArr;
   logic         unpackArr [0:15];
   logic [3:0]    mixedArr [0:7];
   assign out1 = in1 & vdd & ~gnd;
   always_comb begin
      dummy_c c1 = new();
   end
endmodule
module dyn_queue_assoc (
   input  logic        clk,
   output logic [31:0] outv
);
   int dyn_array        [];
   int queue_array      [$];
   int assoc_array      [string];
   int wildcard_array   [*];
   assign outv = 32'd0;
   always_ff @(posedge clk) begin
      dummy_c c2 = new();
   end
endmodule
module func_arglist (
   input  logic [3:0] a,
   output logic [3:0] y
);
   function automatic logic [3:0] sum3 (
      input logic [3:0] x1,
      input logic [3:0] x2,
      input logic [3:0] x3
   );
      sum3 = x1 + x2 + x3;
   endfunction
   logic [3:0] b = 4'h1;
   logic [3:0] c = 4'h2;
   assign y = sum3(a, b, c);
   always_comb begin
      dummy_c c3 = new();
   end
endmodule
module string_attr (
   input  logic dummy_in,
   output logic dummy_out
);
   localparam string STR = "Hello, World!\n";
   (* my_attr = "attribute_value" *) logic sig;
   assign dummy_out = dummy_in & sig;
   always_comb begin
      dummy_c c4 = new();
   end
endmodule
module nested_select (
   input  logic [7:0] idx,
   output logic       sel_out
);
   logic [3:0] dataVec [0:3];
   logic [1:0] inner_index;
   assign inner_index = idx[1:0];
   assign sel_out     = dataVec[1][inner_index];
   always_comb begin
      dummy_c c5 = new();
   end
endmodule
