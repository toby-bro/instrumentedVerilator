interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module BitwiseAssign (
    input logic [3:0] in_a,
    input logic [3:0] in_b,
    output logic [3:0] out_y
);
    assign out_y = in_a ^ in_b;
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_in_a_1755007780169_270,
    input logic [3:0] inj_in_b_1755007780169_103,
    input logic [7:0] inj_in_task_data_1755007780169_117,
    input logic [1:0] inj_in_val_1755007780169_399,
    input logic inj_task_en_1755007780169_445,
    input wire reset,
    output reg inj_out_res_1755007780169_574,
    output logic [3:0] inj_out_y_1755007780169_373,
    output logic inj_task_output_valid_1755007780169_748
);
    // BEGIN: case_basic_ts1755007780169
    // BEGIN: module_task_write_ts1755007780170
    my_if task_vif_inst();
    task automatic update_vif_signals(input logic en, input logic [7:0] data_val,
        output logic [7:0] vif_data, output logic vif_valid, output logic vif_ready);
        if (en) begin
            vif_data = data_val;
            vif_valid = 1'b1;
            vif_ready = 1'b0;
        end else begin
            vif_data = 8'h0;
            vif_valid = 1'b0;
            vif_ready = 1'b1;
        end
    endtask
    always_comb begin
        update_vif_signals(inj_task_en_1755007780169_445, inj_in_task_data_1755007780169_117, task_vif_inst.data, task_vif_inst.valid, task_vif_inst.ready);
        inj_task_output_valid_1755007780169_748 = task_vif_inst.valid;
    end
    // END: module_task_write_ts1755007780170

    always_comb begin
        inj_out_res_1755007780169_574 = 1'b0;
        case (inj_in_val_1755007780169_399)
            2'b00: inj_out_res_1755007780169_574 = 1'b0;
            2'b01: inj_out_res_1755007780169_574 = 1'b1;
            2'b10: inj_out_res_1755007780169_574 = 1'b0;
            2'b11: inj_out_res_1755007780169_574 = 1'b1;
        endcase
    end
    // END: case_basic_ts1755007780169

    BitwiseAssign BitwiseAssign_inst_1755007780169_7510 (
        .in_b(inj_in_b_1755007780169_103),
        .out_y(inj_out_y_1755007780169_373),
        .in_a(inj_in_a_1755007780169_270)
    );
endmodule

