package duplicate_pkg;
  localparam int CONST32 = 32'hDEADBEEF;
endpackage
module dup_const_mod #(parameter WIDTH = 32)
   (input  logic [WIDTH-1:0] in1,
    output logic [WIDTH-1:0] out1);
   import duplicate_pkg::CONST32;
   assign out1 = (CONST32 & CONST32) | ((CONST32 ^ CONST32) & CONST32);
endmodule
module dup_generate_mod
   (input  logic        clk,
    input  logic [3:0]  in_b,
    output logic [3:0]  out_b);
   logic [3:0] tmp [0:3];
   generate
      genvar i;
      for (i = 0; i < 4; i++) begin : gen_loop
         assign tmp[i] = (in_b & 4'hF) ^ 4'h0;
      end
   endgenerate
   always_ff @(posedge clk) begin
      out_b <= tmp[0];
   end
endmodule
module dup_case_mod
   (input  logic [1:0] sel,
    input  logic       a,
    input  logic       b,
    output logic       y);
   always_comb begin
      unique case (sel)
         2'b00: y = a & b;
         2'b01: y = a & b;
         2'b10: y = a & b;
         default: y = a & b;
      endcase
   end
endmodule
module dup_struct_mod
   (input  logic [7:0]  id,
    output logic [31:0] hash);
   typedef struct packed {
      logic [7:0]  a;
      logic [7:0]  b;
      logic [15:0] c;
   } my_s;
   my_s s1 = '{a: id, b: id, c: {id, id}};
   assign hash = {s1.a, s1.b, s1.c};
endmodule
module dup_function_mod
   (input  logic [15:0] din,
    output logic [15:0] dout);
   function automatic logic [15:0] constant();
      constant = 16'hCAFE;
   endfunction
   function automatic logic [15:0] duplicate();
      duplicate = constant();
   endfunction
   assign dout = duplicate() & constant() & din;
endmodule
module dup_union_mod
   (input  logic [7:0] in_u,
    output logic [7:0] out_u);
   typedef union packed {
      logic [7:0]        u8;
      logic signed [7:0] s8;
   } my_u;
   my_u u1;
   always_comb begin
      u1.u8 = in_u;
      out_u = u1.u8 & u1.s8;
   end
endmodule
module dup_array_mod
   (input  logic [7:0] idx,
    output logic [3:0] val_out);
   wire [3:0] arr [0:3][0:3];
   generate
      genvar i, j;
      for (i = 0; i < 4; i++) begin : outer_gen
         for (j = 0; j < 4; j++) begin : inner_gen
            assign arr[i][j] = 4'hA;
         end
      end
   endgenerate
   assign val_out = arr[idx[1:0]][idx[3:2]];
endmodule
