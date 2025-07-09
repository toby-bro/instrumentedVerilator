package net_pkg;
    typedef logic [7:0] byte_t;
    nettype byte_t byte_net_t;
endpackage
import net_pkg::*;
module m_net_types
    (
        input  logic in_sig,
        output logic out_sig
    );
    wire net_single;
    wire [3:0] net_vector;
    assign net_single = in_sig;
    assign out_sig = net_single;
endmodule
module m_user_nettype
    (
        input  byte_t in_data,
        output byte_t out_data
    );
    byte_net_t user_net;
    assign user_net = in_data;
    assign out_data = user_net;
endmodule
module m_rand
    (
        input  logic clk,
        output logic valid
    );
    class RandCls;
        rand bit [3:0] rv;
        randc byte rcv;
        function void init();
            rv = 4'h0;
            rcv = 8'h0;
        endfunction
    endclass
    always_comb begin
        RandCls rc;
        rc = new();
        rc.init();
        valid = clk;
    end
endmodule
module m_dpi
    (
        input  logic [31:0] a,
        output logic [31:0] b
    );
    import "DPI-C" function int dpi_add(input int lhs, input int rhs);
    import "DPI-C" function real dpi_func_real(input int arg);
    assign b = a;
endmodule
module m_seq
    (
        input  logic clk,
        output logic flag
    );
    sequence seqA;
        1'b1;
    endsequence
    property p1;
        @(posedge clk) seqA;
    endproperty
    assert property(p1);
    assign flag = 1'b0;
endmodule
module m_typedef
    (
        input  logic [3:0] a,
        output logic [3:0] y
    );
    typedef logic [3:0] nibble_t;
    nibble_t internal;
    assign internal = a;
    assign y = internal;
endmodule
module m_spec
    (
        input  wire a,
        output wire b
    );
    specify
        specparam WIDTH = 8;
    endspecify
    assign b = a;
endmodule
interface ifc_var;
    logic [7:0] data;
    logic ctrl;
endinterface
