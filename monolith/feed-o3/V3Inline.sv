`timescale 1ns/1ps
interface simple_ifc;
    logic a;
    logic b;
    modport master (input a, output b);
endinterface
module inline_leaf_const #(parameter WIDTH = 1) (
    input  logic in,
    output logic out
);
    assign out = in;
endmodule
module inline_leaf_array (
    input  logic [7:0] in_arr [0:3],
    output logic [7:0] out
);
    assign out = in_arr[0];
endmodule
module inline_ifc_child (
    simple_ifc.master bus,
    output logic      out
);
    assign bus.b = bus.a;
    assign out    = bus.b;
endmodule
module parent_inline (
    input  logic a,
    output logic y
);
    logic t;
    inline_leaf_const leaf (.in(a), .out(t));
    assign y = t;
endmodule
module parent_inline_const (
    input  logic dummy,
    output logic y
);
    inline_leaf_const leaf (.in(1'b1), .out(y));
endmodule
module class_holder (
    input  logic clk,
    output logic out
);
    class counter;
        int cnt;
        function void inc(); cnt++; endfunction
    endclass
    counter c;
    always_ff @(posedge clk) begin
        if (c == null) c = new();
        c.inc();
    end
    assign out = clk;
endmodule
module typedef_user (
    input  logic [7:0] in,
    output logic [7:0] out
);
    typedef logic [7:0] byte_t;
    byte_t local_var;
    always_comb begin
        local_var = in;
    end
    assign out = local_var;
endmodule
module parent_with_ifc (
    input  logic in_sig,
    output logic out_sig
);
    simple_ifc ifc();
    assign ifc.a = in_sig;
    inline_ifc_child child (.bus(ifc), .out(out_sig));
endmodule
