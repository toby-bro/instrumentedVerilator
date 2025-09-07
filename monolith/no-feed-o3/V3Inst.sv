interface bus_if;
    logic data;
endinterface
module leaf (
    input  logic [3:0] in,
    output logic [3:0] out
);
    assign out = in;
endmodule
module iface_leaf (
    bus_if ifx,
    input  logic  ctrl,
    output logic  status
);
    assign ifx.data = ctrl;
    assign status   = ifx.data;
endmodule
module out_mod (
    input  logic        dummy_in,
    output logic [3:0]  data
);
    assign data = {4{dummy_in}};
endmodule
module mid_array (
    input  logic [15:0] in_bus,
    output logic [15:0] out_bus,
    input  logic        ctrl,
    output logic        stat
);
    leaf u_leaf [3:0] ( .in(in_bus), .out(out_bus) );
    bus_if bus_arr[2:0] ();
    iface_leaf u_if_leaf [0:2] ( .ifx(bus_arr), .ctrl(ctrl), .status() );
    iface_leaf u_if_select (
        .ifx   (bus_arr[1]),
        .ctrl  (ctrl),
        .status(stat)
    );
    out_mod u_const (
        .dummy_in (ctrl),
        .data     (4'h0)           
    );
endmodule
module hierarchy_root (
    input  logic [15:0] din,
    output logic [15:0] dout,
    input  logic        ctrl,
    output logic [2:0]  status
);
    mid_array core_inst [3:1] ( .in_bus(din), .out_bus(dout), .ctrl(ctrl), .stat(status) );
endmodule
