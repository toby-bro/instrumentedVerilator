module cycle1(input wire in1, output wire out1);
  wire a, b;
  assign a = b;
  assign b = a;
  assign out1 = in1 ^ a;
endmodule
module cycle2(input logic [3:0] d, output logic [3:0] q_out);
  (* verilator_split_var *) logic [3:0] tmp;
  logic [3:0] q;
  always_comb begin
    tmp = d + q;
    q = tmp - 1;
  end
  assign q_out = q;
endmodule
module case_cycle(input logic sel, input logic d0, input logic d1, output logic y0, output logic y1);
  logic x, y;
  always_comb begin
    case (sel)
      1'b0: begin x = y; y = d0; end
      1'b1: begin y = x; x = d1; end
      default: begin x = 1'b0; y = 1'b0; end
    endcase
  end
  assign y0 = x;
  assign y1 = y;
endmodule
module cond_cycle(input logic c, input logic d0, input logic d1, output logic y0, output logic y1);
  logic u, v;
  always_comb begin
    if (c) begin
      u = v;
      v = d0;
    end else begin
      v = u;
      u = d1;
    end
  end
  assign y0 = u;
  assign y1 = v;
endmodule
module gen_cycle #(parameter N = 4) (input logic [N-1:0] din, output logic [N-1:0] dout);
  logic [N-1:0] vect;
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin : shift
      if (i == 0) begin
        assign vect[0] = vect[N-1];
      end else begin
        assign vect[i] = vect[i-1];
      end
    end
  endgenerate
  assign dout = vect ^ din;
endmodule
module func_cycle(input logic d0, input logic d1, output logic y);
  logic int1, int2;
  function logic f1(input logic x);
    f1 = int2 ^ x;
  endfunction
  function logic f2(input logic x);
    f2 = int1 & x;
  endfunction
  assign int1 = f1(d0);
  assign int2 = f2(d1);
  assign y = int1 | int2;
endmodule
module and_cycle(input logic a_in, input logic b_in, output logic o1, output logic o2, output logic a_out);
  logic a, b;
  assign a = b;
  assign b = a & b_in;
  assign o1 = a & b;
  assign o2 = o1 & b;
  assign a_out = o1;
endmodule
module nested_gen #(parameter M = 3) (input logic [M-1:0] d, output logic [M-1:0] q);
  logic [M-1:0] gvar;
  genvar j;
  generate
    if (M > 2) begin : big
      for (j = 0; j < M; j = j + 1) begin : inner
        assign gvar[j] = (j == M-1) ? gvar[0] : gvar[j+1];
      end
    end else begin : small
      for (j = 0; j < M; j = j + 1) begin : inner2
        assign gvar[j] = (j == M-1) ? gvar[0] : gvar[j+1];
      end
    end
  endgenerate
  assign q = gvar ^ d;
endmodule
