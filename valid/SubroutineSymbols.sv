package dpi_pkg;
    import "DPI-C" function int dpi_sum (input int a, input int b);
endpackage
interface math_ifc;
    function int add1 (input int a);
        add1 = a + 1;
    endfunction
    modport mp (import function int add1 (input int a));
endinterface : math_ifc
interface ext_ifc;
    function int mul2 (input int a);
        mul2 = a * 2;
    endfunction
endinterface : ext_ifc
class BaseClass;
    virtual function int foo (input int a);
        foo = a + 10;
    endfunction
endclass
class DerivedClass extends BaseClass;
    function int foo (input int a);
        foo = super.foo(a) + 1;
    endfunction
endclass
class ExtClass;
    extern function int add (input int a, input int b = 5);
endclass
function int ExtClass::add (input int a, input int b);
    add = a + b;
endfunction
module task_func_mod (
    input  logic                 clk,
    input  logic [7:0]           in_data,
    output logic [7:0]           out_data
);
    task automatic t1 (output logic [7:0] result, ref logic [7:0] val);
        result = val + 1;
        val    = result;
    endtask
    function automatic logic [7:0] f1 (input logic [7:0] val);
        f1 = val + 1;
    endfunction
    always_comb begin
        logic [7:0] temp = in_data;
        logic [7:0] res;
        t1(res, temp);
        out_data = f1(res);
    end
endmodule
module class_virtual_mod (
    input  logic [7:0] in_val,
    output logic [7:0] out_val
);
    DerivedClass d = new();
    always_comb begin
        out_val = d.foo(in_val);
    end
endmodule
module extern_outofblock_mod (
    input  logic [15:0] in1,
    input  logic [15:0] in2,
    output logic [15:0] sum_out
);
    ExtClass ec = new();
    always_comb begin
        sum_out = ec.add(in1, in2);
    end
endmodule
module interface_proto_mod (
    input  logic [31:0] in_val,
    output logic [31:0] out_val
);
    virtual math_ifc.mp vif;
    always_comb begin
        if (vif != null)
            out_val = vif.add1(in_val);
        else
            out_val = in_val;
    end
endmodule
module dpi_mod (
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic [31:0] c
);
    import dpi_pkg::dpi_sum;
    always_comb begin
        c = dpi_sum(a, b);
    end
endmodule
