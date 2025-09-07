interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module mod_fixup_target (
    input logic fs_in_target,
    output logic fs_out_target
);
    assign fs_out_target = fs_in_target;
endmodule

module module_function (
    input wire [7:0] in_func_a,
    input wire [7:0] in_func_b,
    output logic [7:0] out_func_result
);
    function automatic [7:0] add_and_subtract;
    input [7:0] val1;
    input [7:0] val2;
    reg [7:0] temp;
    begin
    temp = val1 + val2;
    add_and_subtract = temp - 1;
    end
    endfunction
    always_comb begin
    out_func_result = add_and_subtract(in_func_a, in_func_b);
    end
endmodule

module module_task_write (
    input logic [7:0] in_task_data,
    input logic task_en,
    output logic task_output_valid
);
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
        update_vif_signals(task_en, in_task_data, task_vif_inst.data, task_vif_inst.valid, task_vif_inst.ready);
        task_output_valid = task_vif_inst.valid;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_fs_in_1755007851485_270,
    input wire [1:0] inj_in_const_index_1755007851486_429,
    input wire [7:0] inj_in_func_a_1755007851485_393,
    input wire [7:0] inj_in_func_b_1755007851485_226,
    input wire [1:0] inj_in_index_1755007851486_242,
    input wire reset,
    output wire inj_fs_out_1755007851485_442,
    output logic [7:0] inj_out_array_sel_const_1755007851486_13,
    output logic [7:0] inj_out_array_sel_var_1755007851486_709,
    output logic [7:0] inj_out_func_result_1755007851485_983,
    output logic inj_task_output_valid_1755007851487_170
);
    // BEGIN: mod_fixup_syntax_user_ts1755007851485
    logic fixup_out_val_ts1755007851485;
        // BEGIN: Mod_ArrayOps_ts1755007851486
        logic [7:0] my_array_ts1755007851486 [3:0];
            module_task_write module_task_write_inst_1755007851487_704 (
                .in_task_data(my_array_ts1755007851486),
                .task_en(fixup_out_val_ts1755007851485),
                .task_output_valid(inj_task_output_valid_1755007851487_170)
            );
        always_comb begin
            my_array_ts1755007851486[0] = inj_in_func_a_1755007851485_393;
            my_array_ts1755007851486[1] = inj_in_func_a_1755007851485_393 + 8'd1;
            my_array_ts1755007851486[2] = inj_in_func_a_1755007851485_393 + 8'd2;
            my_array_ts1755007851486[3] = inj_in_func_a_1755007851485_393 + 8'd3;
            inj_out_array_sel_var_1755007851486_709 = my_array_ts1755007851486[inj_in_index_1755007851486_242];
            inj_out_array_sel_const_1755007851486_13 = my_array_ts1755007851486[inj_in_const_index_1755007851486_429];
        end
        // END: Mod_ArrayOps_ts1755007851486

        module_function module_function_inst_1755007851485_1040 (
            .out_func_result(inj_out_func_result_1755007851485_983),
            .in_func_a(inj_in_func_a_1755007851485_393),
            .in_func_b(inj_in_func_b_1755007851485_226)
        );
    mod_fixup_target fixup_inst (
        .fs_in_target(inj_fs_in_1755007851485_270),
        .fs_out_target(fixup_out_val_ts1755007851485)
    );
    assign inj_fs_out_1755007851485_442 = fixup_out_val_ts1755007851485;
    // END: mod_fixup_syntax_user_ts1755007851485
endmodule

