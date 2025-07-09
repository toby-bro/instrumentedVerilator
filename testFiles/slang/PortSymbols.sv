interface bus_if #(parameter W = 8) ();
    logic clk;
    logic [W-1:0] data;
    modport master (input clk, output data);
    modport slave  (input clk, input data);
endinterface
module ansi_inherit_test
(
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic       c
);
    assign c = ^(a ^ b);
endmodule
module var_inout_test
(
    inout      wire  d,
    input  var logic e,
    output var logic f,
    ref        logic g
);
    assign d = e;
    always_comb f = g;
endmodule
module if_generic
(
    interface i,
    input  logic [7:0] dummy_in,
    output logic [7:0] dummy_out
);
    assign dummy_out = dummy_in;
endmodule
module if_modport_user
(
    bus_if.master m,
    input  logic [7:0] dummy_in,
    output logic [7:0] dummy_out
);
    assign m.data  = dummy_in;
    assign dummy_out = dummy_in;
endmodule
module nonansi_example (p_in, p_out, p_io);
    input  logic p_in;
    output logic p_out;
    inout  wire  p_io;
    assign p_out = p_in;
    assign p_io  = p_in;
endmodule
module nonansi_concat (in0, in1, out_c);
    input  logic in0;
    input  logic in1;
    output logic [1:0] out_c;
    assign out_c = {in0, in1};
endmodule
module uwire_input_test
(
    input  uwire u,
    input  logic in_sig,
    output logic o
);
    assign o = u & in_sig;
endmodule
module generic_iface_mod
(
    interface intf,
    input  logic din,
    output logic dout
);
    assign dout = din;
endmodule
module wrapper
(
    input  logic global_in,
    output logic global_out
);
    bus_if #() bus();
    logic [3:0] a_wire;
    logic [3:0] b_wire;
    wire        c_wire;
    wire        d_wire;
    logic       e_var;
    wire        f_var;
    logic       g_var;
    logic [7:0] dummy_in;
    wire  [7:0] dummy_out;
    wire  [7:0] dummy_out2;
    logic in0;
    logic in1;
    wire  [1:0] out_c;
    uwire u_sig;
    wire p_out_wire;
    wire p_io_wire;
    wire uwire_out;
    wire dout_wire;
    always_comb begin
        a_wire     = {3'b0, global_in};
        b_wire     = ~a_wire;
        e_var      = global_in;
        dummy_in   = {8{global_in}};
        in0        = global_in;
        in1        = ~global_in;
        global_out = c_wire ^ f_var ^ out_c[0] ^ dummy_out[0];
    end
    assign u_sig = global_in;
    ansi_inherit_test u_ansi (
        .a (a_wire),
        .b (b_wire),
        .c (c_wire)
    );
    var_inout_test u_var (
        .d (d_wire),
        .e (e_var),
        .f (f_var),
        .g (g_var)
    );
    if_generic u_ifg (
        .i         (bus),
        .dummy_in  (dummy_in),
        .dummy_out (dummy_out)
    );
    if_modport_user u_ifm (
        .m         (bus.master),
        .dummy_in  (dummy_in),
        .dummy_out (dummy_out2)
    );
    nonansi_example u_nonansi (
        .p_in  (in0),
        .p_out (p_out_wire),
        .p_io  (p_io_wire)
    );
    nonansi_concat u_concat (
        .in0   (in0),
        .in1   (in1),
        .out_c (out_c)
    );
    uwire_input_test u_uwire (
        .u      (u_sig),
        .in_sig (in0),
        .o      (uwire_out)
    );
    generic_iface_mod u_gim (
        .intf (bus),
        .din  (in0),
        .dout (dout_wire)
    );
endmodule
