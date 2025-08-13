timeunit 1ns/1ps;
package common_pkg;
  typedef enum logic [2:0] {S0,S1,S2,S3,S4} state_t;
  typedef struct packed {logic [7:0] payload; state_t state;} packet_t;
endpackage
module m_always_comb(input logic a_i, output logic y_o);
  always_comb y_o = ~a_i;
endmodule
module m_always_ff #(parameter WIDTH=8)(input logic clk_i,input logic rst_ni,input logic [WIDTH-1:0] d_i,output logic [WIDTH-1:0] q_o);
  always_ff @(posedge clk_i or negedge rst_ni) if(!rst_ni) q_o <= '0; else q_o <= d_i;
endmodule
module m_generate(input logic sel_i, output logic [3:0] out_o);
  genvar i;
  generate
    for(i=0;i<4;i++) begin : g
      assign out_o[i] = sel_i ^ i[0];
    end
  endgenerate
endmodule
module m_struct_usage(input common_pkg::packet_t pkt_i, output logic flag_o);
  import common_pkg::*;
  typedef struct packed {logic [7:0] data; logic valid;} local_s;
  local_s loc;
  always_comb begin
    loc.data = pkt_i.payload;
    loc.valid = (pkt_i.state==S2);
    flag_o = loc.valid & ^loc.data;
  end
endmodule
module m_enum_unique(input logic [1:0] sel_i, output logic [3:0] onehot_o);
  typedef enum logic [1:0] {A=2'd0,B=2'd1,C=2'd2} sel_t;
  always_comb begin
    unique case(sel_t'(sel_i))
      A: onehot_o = 4'b0001;
      B: onehot_o = 4'b0010;
      C: onehot_o = 4'b0100;
      default: onehot_o = 4'b1000;
    endcase
  end
endmodule
module m_assert_example(input logic clk_i,input logic rst_ni,input logic req_i,input logic gnt_i,output logic pass_o);
  property p_req_gnt; @(posedge clk_i) disable iff(!rst_ni) req_i |-> ##1 gnt_i; endproperty
  assert property(p_req_gnt);
  assign pass_o = 1'b1;
endmodule
module m_foreach_example(input logic [7:0] vec_i, output logic [15:0] sum_o);
  integer acc;
  always_comb begin
    acc = 0;
    foreach (vec_i[idx]) acc += vec_i[idx];
    sum_o = acc;
  end
endmodule
module m_timeunit_precision(input logic clk_i, output logic tick_o);
  logic local_tick;
  always_ff @(posedge clk_i) local_tick <= ~local_tick;
  assign tick_o = local_tick;
endmodule
