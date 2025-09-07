module param_sub #(
    parameter int    WIDTH = 8,
    parameter string NAME  = "DEF",
    parameter real   SCALE = 1.0,
    parameter type   T     = logic [WIDTH-1:0]
) (
    input  logic [WIDTH-1:0] a,
    output logic [WIDTH-1:0] y
);
    T tmp;
    assign tmp = T'(a);
    assign y   = tmp;
endmodule
interface simple_if #(parameter int W = 8);
    logic [W-1:0] data;
    modport m  (output data);
    modport s  (input  data);
endinterface
module iface_master_use #(
    parameter int W = 8
) (
    simple_if #(W).m bus,
    input  logic in_signal,
    output logic out_signal
);
    assign bus.data   = {W{in_signal}};
    assign out_signal = bus.data[W-1];
endmodule
module iface_slave_use #(
    parameter int W = 8
) (
    simple_if #(W).s bus,
    input  logic in_signal,
    output logic out_signal
);
    assign out_signal = bus.data[0] ^ in_signal;
endmodule
module iface_top (
    input  logic in_sig,
    output logic out_sig
);
    simple_if #(16) bus();
    iface_master_use #(16) u_master (.bus(bus), .in_signal(in_sig), .out_signal());
    iface_slave_use  #(16) u_slave  (.bus(bus), .in_signal(in_sig), .out_signal(out_sig));
endmodule
module array_param_mod #(
    parameter int DATA [0:3] = '{1, 2, 3, 4}
) (
    input  logic in,
    output logic out
);
    assign out = in ^ DATA[0][0];
endmodule
module array_param_user (
    input  logic a,
    output logic b
);
    array_param_mod #(.DATA('{4,3,2,1})) u_arr (.in(a), .out(b));
endmodule
module gen_example #(
    parameter int N = 4
) (
    input  logic  in0,
    output logic  outN
);
    logic [N-1:0] temp;
    generate
        genvar idx;
        for (idx = 0; idx < N; idx = idx + 1) begin : G
            assign temp[idx] = in0;
        end
        if (N > 8) begin
            assign outN = |temp;
        end else begin
            assign outN = &temp;
        end
    endgenerate
endmodule
class my_class #(int W = 8, type DT = int);
    DT data;
    function void set(DT d); data = d; endfunction
endclass
module class_user #(
    parameter int  W  = 8,
    parameter type DT = logic [W-1:0]
) (
    input  logic [W-1:0] din,
    output logic [W-1:0] dout
);
    my_class #(W, DT) c_inst;
    always_comb begin
        c_inst = new();
        c_inst.set(DT'(din));
    end
    assign dout = din;
endmodule
(* verilator hier_block *)
module hier_block_mod #(
    parameter int P0 = 1,
    parameter int P1 = 2
) (
    input  logic i,
    output logic o
);
    localparam int CONST = P0 + P1;
    assign o = i ^ CONST[0];
endmodule
module wrapper1 (
    input  logic in1,
    output logic out1
);
    hier_block_mod #(.P0(3), .P1(4)) u_hb (.i(in1), .o(out1));
endmodule
