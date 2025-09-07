interface example_if; logic sig; endinterface
module simple_ops(input  logic [3:0] a, input  logic [3:0] b,
                  output logic [3:0] sum, output logic [3:0] diff,
                  output logic [3:0] anded, output logic [3:0] ored,
                  output logic [3:0] xored, output logic [3:0] nanded);
  assign sum    = a + b;
  assign diff   = a - b;
  assign anded  = a & b;
  assign ored   = a | b;
  assign xored  = a ^ b;
  assign nanded = ~(a & b);
endmodule
module complex_ops(input  logic       sel,
                   input  logic [7:0] x, input  logic [7:0] y, input  logic [7:0] z,
                   output logic [7:0] m1, output logic [7:0] m2);
  assign m1 = sel ? x : y;
  assign m2 = (x > y) ? z : y;
endmodule
module wide_ops(input  logic [127:0] w1,
                input  logic [127:0] w2,
                output logic [127:0] wadd,
                output logic [127:0] wsub,
                output logic [127:0] wand_out);
  assign wadd     = w1 + w2;
  assign wsub     = w1 - w2;
  assign wand_out = w1 & w2;
endmodule
module slicing_ops(input  logic [15:0] data,
                   output logic [3:0] high, output logic [3:0] low,
                   output logic [3:0] high2, output logic [3:0] low2);
  assign high  = data[15:12];
  assign low   = data[3:0];
  assign high2 = data[8 +: 4];
  assign low2  = data[0 +: 4];
endmodule
module constants(input  logic [3:0] a,
                 output logic [31:0] out1, output logic [31:0] out2,
                 output logic [31:0] out3, output logic [31:0] out4,
                 output logic [31:0] out5, output real         out6,
                 output logic [31:0] out7, output logic [31:0] out8);
  parameter int           P_DEC   = 123;
  parameter [15:0]        P_HEX   = 16'hABCD;
  parameter [7:0]         P_BIN   = 8'b10101010;
  parameter [3:0]         P_OCT   = 4'o7;
  parameter real          P_REAL  = 3.14;
  localparam [255:0]      P_LARGE = 256'hDEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF;
  assign out1 = P_DEC;
  assign out2 = P_HEX;
  assign out3 = P_BIN;
  assign out4 = P_OCT;
  assign out5 = a * P_DEC;
  assign out6 = P_REAL;
  assign out7 = P_LARGE[31:0];
  assign out8 = P_LARGE[255:224];
endmodule
typedef struct packed { logic [3:0] st_x; logic [1:0] st_y; } S_t;
typedef union       { logic [7:0] ubyte; logic [3:0] unib [1:0]; } U_t;
module structs_unions(input  S_t s_in,
                      input  U_t u_in,
                      output logic [5:0] s_pack,
                      output logic [7:0] u_byte,
                      output logic [3:0] u_nib0, output logic [3:0] u_nib1);
  assign s_pack = {s_in.st_x, s_in.st_y};
  assign u_byte = u_in.ubyte;
  assign u_nib0 = u_in.unib[0];
  assign u_nib1 = u_in.unib[1];
endmodule
module dynamic_assoc(input  logic clk, input  logic rst,
                     output logic [7:0] dyn0,
                     output logic [3:0] assoc0);
  logic [7:0] dyn_arr[];
  logic [3:0] assoc_arr[string];
  logic [7:0] dyn_val;
  logic [3:0] assoc_val;
  always_comb begin
    dyn_arr        = new[4];
    dyn_arr[2]     = 8'hFF;
    assoc_arr["k"] = 4'hA;
    dyn_val        = dyn_arr[2];
    assoc_val      = assoc_arr["k"];
  end
  assign dyn0   = dyn_val;
  assign assoc0 = assoc_val;
endmodule
module queue_example(input  logic clk, input  logic rst,
                     output logic [7:0] q0, output logic [7:0] q_last);
  logic [7:0] q[$];
  logic [7:0] q0_int;
  logic [7:0] q_last_int;
  always_comb begin
    q.delete();
    q.push_back(8'hAA);
    q.push_front(8'h55);
    q0_int     = q[0];
    q_last_int = q[q.size()-1];
  end
  assign q0     = q0_int;
  assign q_last = q_last_int;
endmodule
module class_call(input  logic [3:0] in,
                  output logic [3:0] out1, output logic [3:0] out2);
  class C;
    rand logic [3:0] x;
    function logic [3:0] f; return this.x + in; endfunction
    static function logic [3:0] static_f(input logic [3:0] v); return v + 1; endfunction
  endclass
  C c_inst;
  logic [3:0] tmp1;
  logic [3:0] tmp2;
  always_comb begin
    c_inst = new();
    c_inst.x = in;
    tmp1     = c_inst.f();
    tmp2     = C::static_f(in);
  end
  assign out1 = tmp1;
  assign out2 = tmp2;
endmodule
module string_convert(input  logic [7:0] data,
                      output string       out_str);
  string msg;
  always_comb begin
    msg = "";
    $sformat(msg, "Value:%0h", data);
  end
  assign out_str = msg;
endmodule
module array_reset(input  logic clk, input  logic rst,
                   output logic [7:0] arr0, output logic [7:0] arr1, output logic [7:0] arr2);
  logic [7:0] arr [0:3];
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : init_loop
      assign arr[i] = i;
    end
  endgenerate
  assign arr0 = arr[0];
  assign arr1 = arr[1];
  assign arr2 = arr[2];
endmodule
module interface_example(input  logic en, output logic sig_out);
  example_if example_if_inst();
  assign example_if_inst.sig = en;
  assign sig_out = example_if_inst.sig;
endmodule
module cvt_wide_array(input  logic [7:0] src [0:3],
                      output logic [7:0] dst [0:3]);
  assign dst = src;
endmodule
