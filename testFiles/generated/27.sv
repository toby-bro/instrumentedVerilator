interface MyInterface (
    input logic clk
);
    logic req;
    logic valid;
    modport master (output req, input valid, input clk);
    modport slave (input req, output valid, input clk);
endinterface
interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module module_assign_nonblocking (
    input logic clk,
    input logic [7:0] in_value,
    input logic reset,
    output logic out_data_q
);
    my_if vif_inst();
    logic [7:0] data_q;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            vif_inst.data <= 8'h0;
            data_q <= 8'h0;
        end else begin
            vif_inst.data <= in_value;
            data_q <= vif_inst.data;
        end
    end
    assign out_data_q = data_q;
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_in_value_1755004212115_879,
    input wire reset,
    output logic inj_out_data_q_1755004212115_861,
    output logic [7:0] inj_out_vec_1755004212115_83,
    output logic inj_valid_out_1755004212114_786
);
    // BEGIN: ModuleWithInterface_ts1755004212114
    // BEGIN: SimpleLoopExample_ts1755004212115
    always_comb begin
        for (int i = 0; i < 8; i++) begin
            inj_out_vec_1755004212115_83[i] = inj_in_value_1755004212115_879[7 - i];
        end
    end
    // END: SimpleLoopExample_ts1755004212115

    module_assign_nonblocking module_assign_nonblocking_inst_1755004212115_6839 (
        .out_data_q(inj_out_data_q_1755004212115_861),
        .clk(clk),
        .in_value(inj_in_value_1755004212115_879),
        .reset(reset)
    );
    MyInterface my_if (clk);
    assign my_if.req = 1'b1;
    assign inj_valid_out_1755004212114_786 = my_if.valid;
    // END: ModuleWithInterface_ts1755004212114
endmodule

