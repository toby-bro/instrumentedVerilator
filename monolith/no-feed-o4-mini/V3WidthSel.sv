typedef struct packed { logic [7:0] f1; logic [3:0] f2; } my_struct_t;
typedef struct packed { my_struct_t inner; logic [1:0] other; } nested_t;
module selbit_unpacked(input  logic [7:0] a [0:3],
                       input  logic [1:0] idx,
                       output logic [7:0] o);
  assign o = a[idx];
endmodule
module selbit_basic(input  logic [7:0] vec,
                    input  logic [2:0] idx,
                    output logic       bitout);
  assign bitout = vec[idx];
endmodule
module selbit_string(input  string   str,
                     input  int      idx,
                     output byte     ch);
  assign ch = str[idx];
endmodule
module selbit_struct(input  my_struct_t   s_in,
                     input  logic [2:0] idx,
                     output logic [7:0] ofs1);
  assign ofs1 = s_in.f1[idx];
endmodule
module sel_extract_basic(input  logic [15:0] din,
                         input  logic [3:0]  msb,
                         input  logic [3:0]  lsb,
                         output logic [7:0]  dout);
  assign dout = din[msb:lsb];
endmodule
module sel_extract_static(input  logic [15:0] din2,
                          output logic [7:0]  dout2);
  assign dout2 = din2[15:8];
endmodule
module plus_minus_slice(input  logic [15:0] din3,
                        input  logic [3:0]  idx3,
                        output logic [2:0]  dout_p,
                        output logic [2:0]  dout_m);
  assign dout_p = din3[idx3 +: 3];
  assign dout_m = din3[idx3 -: 3];
endmodule
module unpacked_array_extract(input  logic [7:0]   arr_u [0:7],
                               input  logic [3:0]   mi,
                               input  logic [3:0]   li,
                               output logic [7:0]   out_elem,
                               output logic [7:0]   out_slice,
                               output logic [7:0]   out_plus);
  assign out_elem  = arr_u[mi];
  assign out_slice = arr_u[mi:li];
  assign out_plus  = arr_u[mi +: 2];
endmodule
module assoc_array_sel(input  logic [7:0]   aa [string],
                       input  string         key,
                       output logic [7:0]   oaa);
  assign oaa = aa[key];
endmodule
module wildcard_array_sel(input  logic [7:0] wa [*],
                          input  logic [3:0] wi,
                          output logic [7:0] owa);
  assign owa = wa[wi];
endmodule
module dynamic_array_sel(input  logic [7:0] da [],
                         input  logic [3:0] di,
                         output logic [7:0] oda);
  assign oda = da[di];
endmodule
module queue_sel(input  logic [7:0] qvar [$],
                 input  logic [3:0] qi,
                 output logic [7:0] oq_cur,
                 output logic [7:0] oq_last,
                 output logic [7:0] oq_prev);
  assign oq_cur  = qvar[qi];
  assign oq_last = qvar[$];
  assign oq_prev = qvar[$ - 1];
endmodule
module mult_const(input  logic [5:0] idx_m,
                  output logic [15:0] out_mul);
  assign out_mul = idx_m * 8;
endmodule
module sub_neg(input  logic signed [3:0] i_sub,
               output logic signed [3:0] o_sub1,
               output logic signed [3:0] o_sub2);
  assign o_sub1 = i_sub - 2;
  assign o_sub2 = 3 - i_sub;
endmodule
module nested_struct_sel(input nested_t       ns,
                         input logic [2:0]   inx,
                         output logic [7:0]  outn);
  assign outn = ns.inner.f1[inx];
endmodule
