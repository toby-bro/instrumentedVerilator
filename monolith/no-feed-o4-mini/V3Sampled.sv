module sampled_simple(input logic a, output logic b);
  assign b = sampled a;
endmodule
module sampled_array(input logic [3:0] a, output logic b);
  assign b = sampled a[2];
endmodule
module sampled_concat(input logic a, b, c, output logic [2:0] z);
  assign z = sampled {a, b, c};
endmodule
module sampled_chain(input logic x, output logic y);
  assign y = sampled (sampled x);
endmodule
module sampled_partselect(input logic [7:0] a, output logic [3:0] b);
  assign b = sampled a[7:4];
endmodule
module sampled_multi(input logic a, output logic [1:0] z);
  assign z = {1{sampled a}} + {1{sampled a}};
endmodule
module varref_only(input logic p, output logic q);
  assign q = p;
endmodule
module varref_index(input logic [7:0] d, output logic e);
  assign e = d[3];
endmodule
