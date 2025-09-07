interface simple_if;
    logic data;
endinterface
module leaf_basic(
    input  logic a,
    output logic y
);
    assign y = a;
endmodule
module iface_leaf(
    simple_if intf,
    input  logic in,
    output logic out
);
    assign intf.data = in;
    assign out       = intf.data;
endmodule
module expr_connect_module(
    input  logic [1:0] in_bus,
    output logic       out0,
    output logic [1:0] out_bus
);
    leaf_basic u0 (.a(in_bus[0] & in_bus[1]), .y(out0));
    leaf_basic u2 (.a(|in_bus), .y(out_bus[0]));
    leaf_basic u3 (.a(&in_bus), .y(out_bus[1]));
endmodule
module array_inst_module(
    input  logic [1:0] in_vec,
    output logic [1:0] out_vec
);
    leaf_basic inst_arr [1:0] (.a(in_vec), .y(out_vec));
endmodule
module iface_array_module(
    input  logic [3:0] din,
    output logic [3:0] dout
);
    simple_if bus [0:3] ();
    genvar idx;
    generate
        for (idx = 0; idx < 4; idx++) begin : GEN_IF_LEAF
            iface_leaf leaf_i(
                .intf(bus[idx]),
                .in  (din[idx]),
                .out (dout[idx])
            );
        end
    endgenerate
endmodule
module iface_assign_module(
    input  logic ctrl,
    output logic dummy_out
);
    simple_if busA [1:0] ();
    simple_if busB [1:0] ();
    assign busB[0].data = busA[0].data;
    assign busB[1].data = busA[1].data;
    assign dummy_out = ctrl & busB[0].data;
endmodule
module slice_connect_module(
    input  logic [7:0] din,
    output logic [3:0] dout
);
    leaf_basic u_slice [3:0] (.a(din[3:0]), .y(dout));
endmodule
class dummy_class;
    function automatic int foo(int a);
        return a + 1;
    endfunction
endclass
module class_module(
    input  logic clk,
    input  logic in_flag,
    output logic out_val
);
    dummy_class local_obj;
    always_ff @(posedge clk) begin
        local_obj = new();
        out_val <= local_obj.foo(in_flag);
    end
endmodule
