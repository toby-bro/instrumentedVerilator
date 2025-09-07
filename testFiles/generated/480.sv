module ModClockedConditional (
    input logic clk,
    input logic data_in,
    input logic enable,
    output logic data_out
);
    logic reg_data;
    always @(posedge clk) begin
    if (enable) begin
        reg_data <= data_in;
    end
    end
    assign data_out = reg_data;
endmodule

module mod_automatic_task (
    input int i_val,
    output int o_val
);
    task automatic update_val(input int in_v, output int out_v);
        out_v = in_v * 2;
    endtask
    always_comb begin
        int temp_val;
        update_val(i_val, temp_val);
        o_val = temp_val;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_data_in_1755007914652_261,
    input bit [7:0] inj_data_in_1755007914652_505,
    input logic inj_enable_1755007914652_668,
    input int inj_i_val_1755007914652_907,
    input bit inj_select_signal_1755007914652_894,
    input wire reset,
    output logic inj_data_out_1755007914652_454,
    output bit [7:0] inj_data_out_1755007914652_562,
    output int inj_o_val_1755007914652_261
);
    // BEGIN: SimpleLogicTest_ts1755007914652
    logic [7:0] temp_data_ts1755007914652;
        ModClockedConditional ModClockedConditional_inst_1755007914652_7145 (
            .clk(clk),
            .data_in(inj_data_in_1755007914652_261),
            .enable(inj_enable_1755007914652_668),
            .data_out(inj_data_out_1755007914652_454)
        );
    always_comb begin
        if (inj_select_signal_1755007914652_894) begin
            temp_data_ts1755007914652 = inj_data_in_1755007914652_505 + 1;
        end else begin
            temp_data_ts1755007914652 = inj_data_in_1755007914652_505 - 1;
        end
        inj_data_out_1755007914652_562 = temp_data_ts1755007914652;
    end
    // END: SimpleLogicTest_ts1755007914652

    mod_automatic_task mod_automatic_task_inst_1755007914652_175 (
        .i_val(inj_i_val_1755007914652_907),
        .o_val(inj_o_val_1755007914652_261)
    );
endmodule

