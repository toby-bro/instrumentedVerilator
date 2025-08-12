logic root_status;
interface bus_if #(parameter WIDTH = 8);
    logic clk;
    logic [WIDTH-1:0] data;
    modport master (input clk, output data);
    modport slave  (input clk, input data);
endinterface
module iface_producer (
    bus_if.master b,
    input  logic [7:0] in_data,
    output logic       out_flag
);
    assign b.data  = in_data;
    assign out_flag = b.data[0];
endmodule
module iface_consumer (
    bus_if.slave  b,
    input  logic  in_flag,
    output logic [7:0] out_data
);
    assign out_data = b.data ^ {8{in_flag}};
endmodule
module leaf_module #(
    parameter IDX = 0
) (
    input  logic in_bit,
    output logic out_bit
);
    logic internal_signal;
    logic [15:0] vector;
    assign internal_signal = ~in_bit;
    assign vector         = {16{in_bit}};
    assign out_bit        = internal_signal;
    logic use_root;
    assign use_root = root_status;
endmodule
module hier_system (
    input  logic [7:0] in_sig,
    output logic [7:0] out_sig
);
    assign root_status = in_sig[0];
    bus_if #(8) bus();
    logic dummy_flag;
    iface_producer prod_inst (
        .b       (bus),
        .in_data (in_sig),
        .out_flag(dummy_flag)
    );
    logic [7:0] bus_out;
    iface_consumer cons_inst (
        .b       (bus),
        .in_flag (dummy_flag),
        .out_data(bus_out)
    );
    genvar idx;
    for (idx = 0; idx < 4; idx++) begin : gen_leaf
        leaf_module #(.IDX(idx)) u_leaf (
            .in_bit (in_sig[idx]),
            .out_bit()
        );
    end
    logic extracted_bit;
    logic [7:0] vect_low;
    logic [7:0] vect_high;
    assign extracted_bit = gen_leaf[2].u_leaf.internal_signal;
    assign vect_low      = gen_leaf[1].u_leaf.vector[7:0];
    assign vect_high     = gen_leaf[3].u_leaf.vector[15:8];
    assign out_sig = {vect_high[7:3], prod_inst.b.data[2], vect_low[0], extracted_bit};
endmodule
module upward_array_mod (
    input  logic sel,
    output logic val
);
    assign val = sel & root_status;
endmodule
