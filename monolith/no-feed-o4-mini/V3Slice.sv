module slice_select(input logic [7:0] in1, output logic [1:0] out1);
  assign out1 = in1[3 +: 2];
endmodule
module implicit_unpack(input logic [3:0] arr [1:0], output logic [3:0] out2);
  assign out2 = arr[1];
endmodule
module pack_to_array(input logic [7:0] inp, output logic [3:0] arr_out [1:0]);
  assign arr_out = '{inp[7:4], inp[3:0]};
endmodule
module slice_assign(input logic [3:0] a, input logic [1:0] sel, output logic [1:0] out3);
  logic [3:0] tmp;
  always_comb begin
    tmp = a;
    tmp[sel +: 2] = 2'b10;
    out3 = tmp[1 +: 2];
  end
endmodule
module cond_array(input logic c, input logic [3:0] a1, input logic [3:0] a2, output logic [2:0] out4);
  assign out4 = c ? a1[2:0] : a2[2:0];
endmodule
module struct_array(input logic [3:0] in3, output logic [3:0] out5);
  typedef struct packed { logic [3:0] field; } my_struct_t;
  my_struct_t st;
  always_comb begin
    st.field = in3;
    out5 = st.field[3:0];
  end
endmodule
module class_example(input logic clk, input logic rst, input logic d, output logic q);
  class simple_class;
    function logic do_op(logic a);
      return ~a;
    endfunction
  endclass
  simple_class c_inst;
  always_ff @(posedge clk or posedge rst) begin
    if (rst) q <= 1'b0;
    else begin
      c_inst = new();
      q <= c_inst.do_op(d);
    end
  end
endmodule
module eq_expand(input logic [1:0] a [1:0], input logic [1:0] b [1:0], output logic res_and, output logic res_or);
  logic eq0, eq1;
  assign eq0 = (a[0] == b[0]);
  assign eq1 = (a[1] == b[1]);
  assign res_and = eq0 & eq1;
  assign res_or = eq0 | eq1;
endmodule
module neq_expand(input logic [2:0] x [2:0], input logic [2:0] y [2:0], output logic res_nand, output logic res_nor);
  logic ne0, ne1, ne2;
  assign ne0 = (x[0] != y[0]);
  assign ne1 = (x[1] != y[1]);
  assign ne2 = (x[2] != y[2]);
  assign res_nand = ~(ne0 & ne1 & ne2);
  assign res_nor = ~(ne0 | ne1 | ne2);
endmodule
module multi_dim(input logic [3:0] data [1:0][1:0], input logic sel1, input logic sel2, output logic [3:0] outmd);
  assign outmd = data[sel1][sel2];
endmodule
module dyn_array(input logic [1:0] size, input logic [7:0] in, output logic [7:0] outd);
  logic [7:0] dyn_arr[];
  always_comb begin
    dyn_arr = new[size];
    for (int i = 0; i < size; i++)
      dyn_arr[i] = in;
    outd = dyn_arr[size - 1];
  end
endmodule
module queue_example(input logic clk, input logic rst, input logic [7:0] inq, output logic [7:0] outq);
  logic [7:0] qvar[$];
  always_ff @(posedge clk or posedge rst) begin
    if (rst) qvar = {};
    else qvar.push_back(inq);
  end
  assign outq = (qvar.size() > 0) ? qvar[0] : 8'h00;
endmodule
module init_array(input logic [1:0] idx, output logic [3:0] outi);
  logic [3:0] arr_init [0:2] = '{default:4'h0, [1]:4'hA};
  assign outi = arr_init[idx];
endmodule
