interface bus_if;
    logic clk;
    logic data;
    modport master (input clk, output data);
    modport slave  (input clk, input data);
endinterface
module ansi_basic(
    input  logic in_sig,
    output logic out_sig
);
    assign out_sig = in_sig;
endmodule
module ansi_inherit(
    input  logic clk,
           logic a,
    output logic result
);
    assign result = clk & a;
endmodule
module nonansi_implicit(in_val, out_val);
    input  in_val;
    output out_val;
    assign out_val = in_val;
endmodule
module concat_ports({in0, in1}, {out0, out1});
    input  in0, in1;
    output out0, out1;
    assign out0 = in0;
    assign out1 = in1;
endmodule
module interface_port_mod(
    input  logic din,
    input  logic clk,
    output logic dout
);
    bus_if m_if();
    assign m_if.clk = clk;
    assign m_if.data = din;
    assign dout = m_if.data;
endmodule
module modport_port_module(
    input  logic din,
    input  logic clk,
    output logic dout
);
    bus_if s_if();
    assign s_if.clk = clk;
    assign dout = din & s_if.data;
endmodule
module default_port_module(
    input  logic in_signal  = 1'b1,
    output logic out_signal = 1'b0
);
    assign out_signal = in_signal;
endmodule
module ref_port_module(
    input  logic trigger,
    inout  logic value_ref,
    output logic result
);
    assign result = trigger & value_ref;
endmodule
module inout_port_module(
    inout  wire io_line,
    input  wire drive_in,
    output wire drive_out
);
    assign io_line  = drive_in;
    assign drive_out = io_line;
endmodule
module uwire_port_module(
    input  uwire u_sig,
    output logic o_sig
);
    assign o_sig = u_sig;
endmodule
module generic_interface_module(
    input  logic g_in,
    input  logic clk,
    output logic g_out
);
    bus_if gen_if();
    assign gen_if.clk = clk;
    assign gen_if.data = g_in;
    assign g_out = gen_if.data;
endmodule
