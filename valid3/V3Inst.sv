interface bus_if;
    logic d;
    modport master(output d);
    modport slave(input d);
endinterface
module pass_thru4(
    input  logic [3:0] i,
    output logic [3:0] o
);
    assign o = i;
endmodule
module expr_connect_mod(
    input  logic [3:0] a,
    output logic [3:0] y
);
    logic [3:0] t;
    pass_thru4 u0(.i(~a), .o(t));
    assign y = t;
endmodule
module bit_passthrough(
    input  logic in,
    output logic out
);
    assign out = in;
endmodule
module array_inst_mod(
    input  logic [3:0] din,
    output wire [3:0] dout
);
    bit_passthrough inst[3:0](.in(din), .out(dout));
endmodule
module pass_thru1(
    input  logic in,
    output logic out
);
    assign out = in;
endmodule
module output_short_mod(
    input  logic in_sig,
    output logic out_sig
);
    wire short_wire;
    assign short_wire = 1'b0;
    pass_thru1 u_short(.in(in_sig), .out(short_wire));
    assign out_sig = in_sig;
endmodule
module intf_master(
    bus_if.master bus,
    input  logic in_data,
    output logic mirror
);
    assign bus.d = in_data;
    assign mirror = bus.d;
endmodule
module intf_slave(
    bus_if.slave bus,
    input  logic dummy_in,
    output logic out_data
);
    assign out_data = bus.d ^ dummy_in;
endmodule
module interface_array_mod(
    input  logic [1:0] in_sig,
    input  logic [1:0] dummy_vec,
    output wire [1:0] out_sig
);
    bus_if bus_array[1:0]();
    logic [1:0] mirror;
    intf_master m0(bus_array[0], in_sig[0], mirror[0]);
    intf_master m1(bus_array[1], in_sig[1], mirror[1]);
    intf_slave s0(bus_array[0], dummy_vec[0], out_sig[0]);
    intf_slave s1(bus_array[1], dummy_vec[1], out_sig[1]);
endmodule
