package my_pkg;
endpackage: my_pkg
module CFuncExample(input logic clk_cfe, output logic out_cfe);
  function automatic void funcEmpty(input bit a, output bit b);
  endfunction
  function automatic int funcReturn(input bit x);
    return x;
  endfunction
endmodule
module DPIImportExample(input logic in_dpi, output logic out_dpi);
  import "DPI-C" function int dpifunc(input logic a, inout shortint b, output bit c);
endmodule
module DPIExportExample(input logic clk_dpe, output logic [3:0] out_dpe);
  function void expfunc(input logic a);
  endfunction
  export "DPI-C" function expfunc;
endmodule
module VarDeclExample(input logic [7:0] in_vd, output logic [15:0] out_vd);
  wire [3:0] w1;
  wire signed [15:0] w2 [2:0];
  reg [31:0] reg_data;
  bit readonly_flag;
  localparam int LOCAL_CONST = 5;
  string str_dpi_tmp;
endmodule
module ClassExample(input logic clk_ce, output logic out_ce);
  class Base;
    function new();
    endfunction
    function void delete();
    endfunction
    virtual function int virtFunc(input int a);
    endfunction
  endclass
  class Derived extends Base;
    function new();
      super.new();
    endfunction
    virtual function int virtFunc(input int a);
      return a + 1;
    endfunction
  endclass
  always_ff @(posedge clk_ce) begin
    static Derived d_inst = new();
    static Base b_inst = new();
  end
endmodule
module AccessorExample(input logic in_acc, output logic out_acc);
  reg __Vm_sig_data;
  function logic get_data();
    return __Vm_sig_data;
  endfunction
  function void set_data(input logic v);
    __Vm_sig_data = v;
  endfunction
endmodule
module TextSectionExample(input logic in_ts, output logic out_ts);
  localparam string systemc_class_name = "TextSectionExample";
  localparam string text_section = "Some SystemC code snippet";
endmodule
module ModCUseExample(input logic in_mc, output logic out_mc);
  import my_pkg::*;
endmodule
module GenerateExample(input logic in_gen, output logic [1:0] out_gen);
  genvar i;
  generate
    for (i = 0; i < 2; i = i + 1) begin : genb
      logic signed [3:0] arr [3];
    end
  endgenerate
endmodule
module ParamExample #(parameter int P = 4)(input logic in_pe, output logic [7:0] out_pe);
  localparam int LP = P + 1;
  assign out_pe = in_pe ? LP : P;
endmodule
