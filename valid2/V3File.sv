package math_pkg;
   function automatic int add(input int a, b);
      return a + b;
   endfunction
endpackage
module arithmetic_example(
   input  logic        clk,
   input  logic [31:0] a,
   input  logic [31:0] b,
   output logic [31:0] sum
);
   always_ff @(posedge clk) begin
      sum <= a + b;
   end
endmodule
module casex_casez_demo(
   input  logic [3:0] sel,
   output logic [3:0] y
);
   logic [3:0] temp;
   always_comb begin
      unique casex (sel)
         4'b1xxx: temp = 4'hF;
         4'b01xx: temp = 4'hE;
         default: temp = 4'h0;
      endcase
      casez (sel)
         4'bzzzz: y = 4'h0;
         4'b??01: y = temp;
         default: y = temp ^ 4'hA;
      endcase
   end
endmodule
module class_demo(
   input  logic        clk,
   input  logic [7:0]  in_data,
   output logic [7:0]  out_data
);
   class simple_class;
      int data;
      function new(); data = 0; endfunction
      function int incr(input int v); data += v; return data; endfunction
   endclass
   simple_class obj;
   always_ff @(posedge clk) begin
      if (obj == null) obj = new();
      out_data <= obj.incr(in_data);
   end
endmodule
module task_function_demo(
   input  logic din,
   output logic dout
);
   task automatic invert(input logic v, output logic o);
      o = ~v;
   endtask
   always_comb begin
      invert(din, dout);
   end
endmodule
module struct_union_demo(
   input  logic [15:0] data_in,
   output logic [7:0]  data_out
);
   typedef struct packed {
      logic [7:0] lo;
      logic [7:0] hi;
   } split_s;
   split_s s;
   always_comb begin
      s = data_in;
      data_out = s.lo ^ s.hi;
   end
endmodule
module package_user(
   input  logic [7:0] a,
   input  logic [7:0] b,
   output logic [8:0] sum
);
   import math_pkg::*;
   always_comb begin
      sum = add(a, b);
   end
endmodule
module generate_demo #(
   parameter WIDTH = 4
)(
   input  logic [WIDTH-1:0] in_vec,
   output logic [WIDTH-1:0] out_vec
);
   generate
      genvar i;
      for (i = 0; i < WIDTH; i = i + 1) begin : g
         assign out_vec[i] = ~in_vec[i];
      end
   endgenerate
endmodule
module labeled_blocks_demo(
   input  logic in_sig,
   output logic out_sig
);
   always_comb begin : main_block
      if (in_sig) begin : label_true
         out_sig = 1'b1;
      end else begin : label_false
         out_sig = 1'b0;
      end
   end
endmodule
module enum_state_demo(
   input  logic clk,
   input  logic rst,
   output logic state_bit
);
   typedef enum logic [1:0] {S0, S1, S2} state_t;
   state_t state;
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
         state <= S0;
      end else begin
         case (state)
            S0: state <= S1;
            S1: state <= S2;
            default: state <= S0;
         endcase
      end
   end
   assign state_bit = state[0];
endmodule
