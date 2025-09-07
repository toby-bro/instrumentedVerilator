interface bus_if #(parameter int DW = 8) (input logic clk);
    logic [DW-1:0] data;
    modport master (input data, clk);
    modport slave  (output data, clk);
endinterface
package util_pkg;
    parameter int PVAL = 16;
    typedef struct packed {logic [3:0] a; logic [3:0] b;} pair_t;
    function int add(input int x, input int y);
        return x + y;
    endfunction
    export "DPI-C" function add;
endpackage
class base_c;
    virtual function int foo();
        return 0;
    endfunction
endclass
class derived_c extends base_c;
    virtual function int foo();
        return 1;
    endfunction
endclass
module child_mod #(parameter int DW = 8) (
    input  logic                clk,
    input  logic [DW-1:0]       in_data,
    output logic [DW-1:0]       out_data
);
    assign out_data = in_data;
endmodule
module parent_mod #(parameter int DW = 8) (
    input  logic                clk,
    input  logic [DW-1:0]       a,
    output logic [DW-1:0]       b
);
    child_mod #(.DW(DW)) u_child (.*); 
endmodule
module pkg_user (
    input  logic [31:0] in_val,
    output logic [31:0] out_val
);
    import util_pkg::*;
    assign out_val = add(in_val, PVAL);
endmodule
module bind_target (
    input  logic sig_in,
    output logic sig_out
);
    assign sig_out = sig_in;
endmodule
module bind_checker (
    input  logic sig_in,
    output logic sig_out
);
    assign sig_out = ~sig_in;
endmodule
module bind_wrapper (
    input  logic d_in,
    output logic d_out
);
    bind bind_target bind_checker checker_inst (.*);
    assign d_out = d_in;
endmodule
module iface_user (
    bus_if.master intf,
    input  logic                 clk,
    input  logic                 en,
    output logic [bus_if.DW-1:0] value
);
    assign value = en ? intf.data : '0;
endmodule
module vif_user (
    input  logic clk,
    output logic flag
);
    bus_if #(8) if_inst(clk);
    virtual bus_if.slave vif;
    assign flag = if_inst.data[0];
endmodule
module rec_mod #(parameter int N = 0) (
    input  logic in_sig,
    output logic out_sig
);
    generate
        if (N == 0) begin : base_case
            assign out_sig = in_sig;
        end else begin : recurse_case
            rec_mod #(N-1) u_rec (.in_sig(in_sig), .out_sig(out_sig));
        end
    endgenerate
endmodule
module rec_root (
    input  logic in_sig,
    output logic out_sig
);
    rec_mod #(2) inst (.in_sig(in_sig), .out_sig(out_sig));
endmodule
module default_port_mod (
    input  logic a = 1'b0,
    output logic b = 1'b0
);
    assign b = a;
endmodule
module dp_user (
    input  logic  x,
    output logic  y
);
    default_port_mod u1 (.b(y)); 
    assign y = x;
endmodule
module class_user (
    input  logic clk,
    output logic valid
);
    derived_c obj = new();
    assign valid = obj.foo();
endmodule
