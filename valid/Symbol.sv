package pkg_types;
   typedef logic [7:0] byte_t;
   typedef struct packed {logic [3:0] lo, hi;} nibble_pair_t;
   typedef union  packed {nibble_pair_t np; logic [7:0] raw;} nibble_u_t;
endpackage
class rand_class;
   rand bit val;
   function new();
      val = $urandom_range(0, 1);
   endfunction
endclass
interface simple_if #(parameter WIDTH = 8) (input logic clk);
   logic [WIDTH-1:0] data;
   modport master (input  clk, output data);
   modport slave  (input  clk, input  data);
endinterface
module alias_subroutine(input  logic [7:0] din,
                        output logic [7:0] dout);
   import pkg_types::byte_t;
   function byte_t swap_bits(byte_t v);
      swap_bits = {v[3:0], v[7:4]};
   endfunction
   assign dout = swap_bits(din);
endmodule
module generate_example #(parameter N = 4)
                         (input  logic [N-1:0] in,
                          output logic [N-1:0] out);
   genvar i;
   generate
      for (i = 0; i < N; i++) begin : gen_blk
         if (i % 2 == 0) begin : even_blk
            assign out[i] = in[i];
         end
         else begin : odd_blk
            logic tmp;
            assign tmp    = in[i];
            assign out[i] = tmp;
         end
      end
   endgenerate
endmodule
module interface_master(input  logic        clk,
                        input  logic [7:0]  in,
                        output logic [7:0]  out);
   simple_if #(8) sif (clk);
   assign sif.data = in;
   assign out      = sif.data;
endmodule
module interface_slave(input  logic        clk,
                       output logic [7:0]  out);
   simple_if #(8) sif (clk);
   assign out = sif.data;
endmodule
module primitive_example(input  logic a,
                         input  logic b,
                         output logic y);
   wire gate_out;
   and gate1 (gate_out, a, b);
   (* keep = "true" *) wire attr_wire = gate_out;
   assign y = attr_wire;
endmodule
module classrand_example(input  logic in,
                         output logic out);
   rand_class rc;
   always_comb begin
      rc = new;
      out = rc.val ^ in;
   end
endmodule
module def_child #(parameter WIDTH = 1)
                  (input  logic in,
                   output logic out);
   assign out = in;
endmodule
module defparam_example(input  logic a,
                        output logic b);
   def_child u0 (.in(a), .out(b));
   defparam u0.WIDTH = 4;
endmodule
module struct_union_example(input  logic [31:0] in,
                            output logic [31:0] out);
   typedef struct packed {logic [15:0] lo; logic [15:0] hi;} packed_struct_t;
   typedef union  packed {packed_struct_t s; logic [31:0] full;} packed_union_t;
   packed_union_t u;
   typedef struct {logic [7:0] a; logic [7:0] b;} unpacked_struct_t;
   unpacked_struct_t us;
   always_comb begin
      u.full = in;
      us.a   = u.s.lo[7:0];
      us.b   = u.s.hi[7:0];
      out    = {u.s.hi, u.s.lo};
   end
endmodule
