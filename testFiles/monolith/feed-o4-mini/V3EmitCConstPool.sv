class DummyClass;
  function logic do_something(input logic a);
    return a;
  endfunction
endclass
module MNoConst(input logic clk, output logic out);
  assign out = clk;
endmodule
module MSimpleConst(input logic in, output logic [3:0] out);
  localparam [3:0] P = 4;
  assign out = in ? P : 0;
endmodule
module MWideConst(input logic in, output logic [31:0] out);
  localparam [63:0] P = 64'h0123456789ABCDEF;
  assign out = in ? P[31:0] : P[63:32];
endmodule
module MStringConst(input logic in, output logic out);
  localparam string S = "Hello";
  assign out = in;
endmodule
module MUnpackedArray(input logic [1:0] in, output logic [7:0] out);
  localparam [7:0] A [0:3] = '{8'd1, 8'd2, 8'd3, 8'd4};
  assign out = A[in];
endmodule
module MMultiDimArray(input logic [1:0] sel, output logic [3:0] out);
  localparam [3:0] B [1:0][1:0] = '{'{4'd1, 4'd2}, '{4'd3, 4'd4}};
  assign out = B[sel[1]][sel[0]];
endmodule
module MStructConst(input logic sel, output logic [1:0] out);
  typedef struct packed { logic [1:0] x; logic [1:0] y; } S;
  localparam S s = '{x:2, y:1};
  assign out = sel ? s.x : s.y;
endmodule
module MGenerateConsts(input logic in, output logic out);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : genC
      localparam [3:0] C = i;
    end
  endgenerate
  assign out = in;
endmodule
module MClassInst(input logic in, output logic out);
  always_comb begin
    DummyClass c = new;
    out = c.do_something(in);
  end
endmodule
module MFunction(input logic [3:0] in, output logic [3:0] out);
  function automatic logic [3:0] f(input logic [3:0] v);
    return v + 1;
  endfunction
  assign out = f(in);
endmodule
module MCase(input logic [1:0] sel, output logic [7:0] out);
  always_comb begin
    case (sel)
      2'b00: out = 8'd0;
      2'b01: out = 8'd1;
      default: out = 8'd255;
    endcase
  end
endmodule
