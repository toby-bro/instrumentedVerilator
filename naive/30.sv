package common_pkg;
   typedef struct packed {
      logic [3:0] a;
      logic [3:0] b;
   } pair_t;
   function automatic logic [4:0] add4 (input logic [3:0] x, y);
      add4 = x + y;
   endfunction
endpackage
import common_pkg::*;
module arith_unit #(
   parameter int WIDTH = 8
) (
   input  logic [WIDTH-1:0] in_a,
   input  logic [WIDTH-1:0] in_b,
   input  logic             sub,
   output logic [WIDTH-1:0] result
);
   logic [WIDTH:0] sum;
   always_comb begin
      if (sub)
         sum = in_a - in_b;
      else
         sum = in_a + in_b;
   end
   assign result = sum[WIDTH-1:0];
   property no_overflow_add;
      @(posedge sub) !sum[WIDTH];
   endproperty
   assert property(no_overflow_add);
endmodule
module fsm_sync (
   input  logic clk,
   input  logic rst_n,
   input  logic in_sig,
   output logic out_sig
);
   typedef enum logic [1:0] { IDLE, STATE1, STATE2 } state_t;
   state_t state, next_state;
   always_comb begin
      next_state = state;
      out_sig    = 1'b0;
      case (state)
         IDLE:    if (in_sig)     next_state = STATE1;
         STATE1:  begin
                     out_sig = 1'b1;
                     if (!in_sig) next_state = STATE2;
                  end
         STATE2:  if (in_sig)     next_state = IDLE;
         default:                 next_state = IDLE;
      endcase
   end
   always_ff @(posedge clk or negedge rst_n) begin
      if (!rst_n)
         state <= IDLE;
      else
         state <= next_state;
   end
endmodule
module class_example #(
   parameter int W = 8
) (
   input  logic             clk,
   input  logic             rst_n,
   input  logic [W-1:0]     seed,
   output logic [W-1:0]     value
);
   class VarClass;
      logic [W-1:0] v;
      function void compute (input logic [W-1:0] s);
         v = ~s;
      endfunction
   endclass
   VarClass vc;
   always_ff @(posedge clk or negedge rst_n) begin
      if (!rst_n) begin
         value <= '0;
         vc = null;
      end
      else begin
         if (vc == null)
            vc = new();
         vc.compute(seed);
         value <= vc.v;
      end
   end
endmodule
module gen_array #(
   parameter int N = 4,
   parameter int W = 8
) (
   input  logic [W-1:0] din [N],
   output logic [W-1:0] dout[N]
);
   genvar i;
   generate
      for (i = 0; i < N; i = i + 1) begin : gen_assign
         assign dout[i] = din[i] + W'(i);
      end
   endgenerate
endmodule
module struct_example (
   input  logic        clk,
   input  logic [7:0]  in_data,
   output logic [7:0]  out_data
);
   typedef struct packed {
      logic [3:0] lo;
      logic [3:0] hi;
   } byte_t;
   byte_t data_s;
   always_ff @(posedge clk) begin
      data_s.lo <= in_data[3:0];
      data_s.hi <= in_data[7:4];
      out_data  <= {data_s.hi, data_s.lo};
   end
endmodule
