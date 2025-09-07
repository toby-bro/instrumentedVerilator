package pkg1;
    typedef logic [7:0] pkg_t;
endpackage
interface intf1;
    logic sig;
    logic outp;
    modport mp1 (input sig, output outp);
endinterface
class cls1;
    rand bit [3:0] rv;
    function new();
    endfunction
    function bit do_tsk(bit x);
        do_tsk = x;
    endfunction
endclass
class cls2 extends cls1;
    function new();
        super.new();
    endfunction
endclass
module test_params (input logic in, output logic out);
    import pkg1::*;
    typedef logic [3:0] myt;
    parameter int P = 4;
    localparam int LP = P + 2;
    myt x = LP;
    assign out = in & x[0];
endmodule
module test_generate (input logic in, output logic out);
    genvar i;
    generate
        for (i = 0; i < 2; i = i + 1) begin : genblk
            logic tmp;
            assign tmp = in;
        end
    endgenerate
    assign out = genblk[0].tmp;
endmodule
module test_foreach (input logic [3:0] in, output logic [3:0] out);
    logic [3:0] arr;
    integer idx;
    always_comb begin
        foreach (arr[idx])
            arr[idx] = in[idx];
    end
    assign out = arr;
endmodule
module test_struct_union_enum (input logic s, output logic e_out);
    typedef struct { logic a; logic b; } st_t;
    typedef union { logic u; logic v; } un_t;
    enum bit [1:0] {A = 2'b00, B = 2'b01, C = 2'b10} e;
    st_t st1;
    un_t un1;
    assign st1 = '{a: s, b: 1'b0};
    assign un1.u = st1.b;
    assign e_out = (e == B);
endmodule
module test_class_usage (input logic clk, output logic out);
    cls2 c;
    always_ff @(posedge clk) begin
        c = new();
        c.rv = c.rv + 1;
        out <= c.do_tsk(c.rv[0]);
    end
endmodule
module test_interface_modport (input logic sig, input logic in, output logic out);
    intf1 ifc();
    assign out = ifc.sig & sig & in;
endmodule
module test_package_import (input logic in, output logic out);
    import pkg1::*;
    pkg_t var = 8'hFF;
    assign out = in & var[0];
endmodule
module test_typedef_scope (input logic in, output logic out);
    typedef logic temp_t;
    generate
        begin : namedblk
            temp_t temp = in;
            assign out = temp;
        end
    endgenerate
endmodule
