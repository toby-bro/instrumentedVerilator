package my_pkg;
typedef enum logic [1:0] {IDLE = 2'd0, BUSY = 2'd1, DONE = 2'd2, ERR = 2'd3} state_e;
class rand_class;
typedef struct {
  rand bit [7:0] data_array[];
  rand bit [7:0] q[$];
  rand bit [7:0] a_map[int];
  rand bit flag;
} rand_unp_s;
typedef struct packed {
  logic [7:0] data;
  state_e st;
} rand_pack_s;
typedef union packed {
  logic [9:0] as_bits;
  rand_pack_s as_struct;
} rand_union_u;
rand_unp_s unp_var;
rand_pack_s pack_var;
rand_union_u uni_var;
function automatic int incr(input int v);
  incr = v + 1;
endfunction
endclass
endpackage
module child_mod(
  input  logic in_sig,
  output logic out_sig
);
assign out_sig = in_sig;
endmodule
module parent_mod(
  input  logic a,
  output logic y
);
logic w;
child_mod u_child (.in_sig(a), .out_sig(w));
assign y = w;
endmodule
module param_genvar_mod #(
  parameter int WIDTH = 8,
  parameter logic [3:0] CONST_VAL = 4'hA
)(
  input  logic [WIDTH-1:0] in_vec,
  output logic [WIDTH-1:0] out_vec
);
genvar i;
generate
  for (i = 0; i < WIDTH; i++) begin : g_assign
    assign out_vec[i] = in_vec[i] ^ CONST_VAL[i % 4];
  end
endgenerate
endmodule
module struct_packed_mod(
  input  logic       clk,
  input  logic       rst_n,
  output logic [25:0] out_bits
);
import my_pkg::*;
typedef struct packed {
  logic [7:0]  a;
  logic [15:0] b;
  state_e      s;
} my_pack_t;
typedef struct {
  logic [3:0] arr[0:3];
  logic [7:0] bytes;
} my_unp_t;
typedef union packed {
  logic [25:0] as_word;
  my_pack_t    as_struct;
} my_union_t;
my_union_t reg_u;
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    reg_u.as_word <= 26'h0;
  end
end
assign out_bits = reg_u.as_word;
endmodule
module dpi_mod(
  input  logic [31:0] din,
  output logic [31:0] dout
);
import "DPI-C" function int c_add_one(input int a);
export "DPI-C" function sv_add_one;
function int sv_add_one(input int a);
  sv_add_one = a + 1;
endfunction
always_comb begin
  dout = c_add_one(int'(din));
end
endmodule
module class_inst_mod(
  input  logic clk,
  input  logic rst_n,
  output logic [7:0] data_o
);
import my_pkg::*;
rand_class rc;
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    rc = new();
    data_o <= '0;
  end else begin
    data_o <= rc.pack_var.data;
  end
end
endmodule
