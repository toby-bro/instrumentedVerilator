module supply_expr_mod (input  logic in, output wire out);
  supply0 s0;
  supply1 s1;
  wire temp;
  assign temp = in & s1;
  assign out  = temp | s0;
endmodule
module array_example #(parameter WIDTH = 8) (
  input  logic clk,
  input  logic [WIDTH-1:0] in,
  output logic out
);
  logic [3:0] packedArr;
  logic unpackArr [0:3];
  logic [1:0] multi [0:1][0:2];
  int da[];
  byte q[$];
  int aa[string];
  bit wa[*];
  always_ff @(posedge clk) begin
    packedArr <= 4'hF;
    unpackArr[0] <= in[0];
    multi[0][0] <= in[1:0];
    if (da.size() == 0) begin
      da = new[2];
      da[0] <= 1;
      da[1] <= 2;
    end
    q.push_front(8'hAA);
    aa["k"] <= 42;
    wa[0]   <= 1'b1;
    out <= packedArr[0] ^ unpackArr[0] ^ q[0][0];
  end
endmodule
module arglist_example (
  input  logic [7:0] a,
  input  logic [7:0] b,
  output logic [7:0] y
);
  function automatic [7:0] add_three (logic [7:0] x, logic [7:0] y_in, logic [7:0] z);
    add_three = x + y_in + z;
  endfunction
  always_comb begin
    y = add_three(a, b, 8'h1);
  end
endmodule
module reset_passthrough (
  input  logic clk,
  input  logic rst_n,
  input  logic sig,
  output logic out
);
  always_ff @(posedge clk) begin
    if (!rst_n) out <= 1'b0;
    else        out <= sig;
    assert (rst_n || !rst_n);
  end
endmodule
module genvar_example (
  input  logic a,
  output logic [1:0] y
);
  genvar i;
  generate
    for (i = 0; i < 2; i = i + 1) begin : gen_blk
      assign y[i] = a;
    end
  endgenerate
endmodule
