module leaf_simple (
    input  logic [7:0] d,
    output logic [7:0] q
);
    assign q = d;
endmodule
module leaf_flipflop (
    input  logic clk,
    input  logic din,
    output logic q
);
    logic r;
    always_ff @(posedge clk)
        r <= din;
    assign q = r;
endmodule
module child4 (
    input  logic [3:0] d,
    output logic [3:0] q
);
    assign q = d;
endmodule
module child8 (
    input  logic [7:0] d,
    output logic [7:0] q
);
    assign q = d;
endmodule
interface ifbus;
    logic data;
endinterface
module intf_consumer (
    ifbus           b,
    input  logic    sel,
    output logic    out
);
    assign out = sel ? b.data : 1'b0;
endmodule
module parent_array (
    input  logic [31:0] din,
    output logic [31:0] dout
);
    logic [7:0] seg_in  [0:3];
    logic [7:0] seg_out [0:3];
    assign seg_in[0] = din[ 7: 0];
    assign seg_in[1] = din[15: 8];
    assign seg_in[2] = din[23:16];
    assign seg_in[3] = din[31:24];
    leaf_simple u_leaf [0:3] ( .d(seg_in), .q(seg_out) );
    assign dout = { seg_out[3], seg_out[2], seg_out[1], seg_out[0] };
endmodule
module parent_extend (
    input  logic [3:0] din,
    output logic [7:0] dout
);
    child8 u_ext ( .d(din), .q(dout) );   
endmodule
module parent_slice (
    input  logic [7:0] din,
    output logic [3:0] dout
);
    child4 u_sel ( .d(din[3:0]), .q(dout) );   
endmodule
module intf_parent (
    input  logic [1:0] sel,
    output logic [1:0] out
);
    ifbus bus_array [0:1] ();
    assign bus_array[0].data = sel[0];
    assign bus_array[1].data = sel[1];
    logic sel_arr [0:1];
    assign sel_arr[0] = sel[0];
    assign sel_arr[1] = sel[1];
    logic out_arr [0:1];
    intf_consumer consumers [0:1] ( bus_array, sel_arr, out_arr );
    assign out = { out_arr[1], out_arr[0] };
endmodule
module intf_index_user (
    ifbus        b,
    output logic out
);
    assign out = b.data;
endmodule
module intf_index_parent (
    input  logic sel,
    output logic out
);
    ifbus bus_arr [0:3] ();
    assign bus_arr[2].data = sel;
    intf_index_user iu ( .b(bus_arr[2]), .out(out) );
endmodule
