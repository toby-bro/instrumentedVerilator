module mod_unused_ports (
    input wire unused_in,
    output logic unused_out
);
    assign unused_out = unused_in;
endmodule

module module_task_args (
    input logic [7:0] arg_in_task,
    input logic [7:0] data_a_init_task,
    input logic start_task,
    output logic [7:0] data_a_out_task,
    output logic [7:0] data_b_out_task
);
    logic [7:0] data_a ;
    logic [7:0] data_b ;
    task automatic modify_vars;
        input logic [7:0] task_arg;
        logic [7:0] task_local ;
        begin
            task_local = task_arg;
            data_a = task_local + 8'd1;
            data_b = task_arg - 8'd1;
        end
    endtask
    always_comb begin
        if (start_task) begin
            data_a = data_a_init_task;
            data_b = 8'hFF;
            modify_vars(arg_in_task);
        end else begin
            data_a = 8'h00;
            data_b = 8'h00;
        end
    end
    always_comb begin
        data_a_out_task = data_a + 8'd2;
        data_b_out_task = data_b;
    end
endmodule

module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
endmodule

module module_using_package_param (
    input logic [31:0] wide_data_in,
    output logic [31:0] wide_data_out
);
    assign wide_data_out = wide_data_in;
endmodule

module target_module_for_bind (
    input logic i_target_clk,
    input logic [7:0] i_target_data,
    output logic [7:0] o_target_result
);
    always_comb o_target_result = i_target_data + 1;
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_arg_in_task_1755007874206_869,
    input logic inj_b_1755007874208_344,
    input logic [7:0] inj_data_a_init_task_1755007874206_500,
    input wire inj_g_ctrl_p_1755007874206_480,
    input logic [3:0] inj_i_control_1755007874207_476,
    input logic [1:0] inj_in_val_1755007874206_692,
    input logic inj_start_task_1755007874206_907,
    input logic [31:0] inj_wide_data_in_1755007874208_104,
    input wire reset,
    output logic [7:0] inj_data_a_out_task_1755007874206_760,
    output logic [7:0] inj_data_b_out_task_1755007874206_268,
    output wire inj_data_d_1755007874207_721,
    output wire inj_g_out_and_1755007874206_2,
    output wire inj_g_out_or_1755007874206_780,
    output logic inj_o_1755007874207_67,
    output logic [7:0] inj_o_result_1755007874207_413,
    output logic inj_o_status_1755007874207_104,
    output reg inj_out_res_1755007874206_649,
    output logic inj_sum_1755007874208_40,
    output logic inj_unused_out_1755007874206_212,
    output logic [31:0] inj_wide_data_out_1755007874208_948
);
    // BEGIN: Module_GatePrimitives_ts1755007874206
    // BEGIN: case_single_default_after_item_ts1755007874206
    // BEGIN: simple_logic_b_ts1755007874207
    // BEGIN: child_module_v1_config_dummy_ts1755007874207
    // BEGIN: bind_directive_top_ts1755007874208
    // BEGIN: simple_adder_ts1755007874208
    module_using_package_param module_using_package_param_inst_1755007874208_8578 (
        .wide_data_in(inj_wide_data_in_1755007874208_104),
        .wide_data_out(inj_wide_data_out_1755007874208_948)
    );
    assign inj_sum_1755007874208_40 = inj_start_task_1755007874206_907 + inj_b_1755007874208_344;
    // END: simple_adder_ts1755007874208

    target_module_for_bind target_inst(
        .i_target_clk   (clk),
        .i_target_data  (inj_arg_in_task_1755007874206_869),
        .o_target_result(inj_o_result_1755007874207_413)
    );
    module_to_bind bind_inst(
        .i_bind_clk     (clk),
        .i_bind_control (inj_i_control_1755007874207_476),
        .o_bind_status  (inj_o_status_1755007874207_104)
    );
    // END: bind_directive_top_ts1755007874208

    assign inj_o_1755007874207_67 = ~inj_start_task_1755007874206_907; 
    // END: child_module_v1_config_dummy_ts1755007874207

    assign inj_data_d_1755007874207_721 = reset;
    // END: simple_logic_b_ts1755007874207

    always_comb begin
        inj_out_res_1755007874206_649 = 1'b0;
        case (inj_in_val_1755007874206_692)
            2'b01: inj_out_res_1755007874206_649 = 1'b1;
            default: inj_out_res_1755007874206_649 = 1'b0;
            2'b10: inj_out_res_1755007874206_649 = 1'b1;
        endcase
    end
    // END: case_single_default_after_item_ts1755007874206

    module_task_args module_task_args_inst_1755007874206_6947 (
        .data_a_init_task(inj_data_a_init_task_1755007874206_500),
        .start_task(inj_start_task_1755007874206_907),
        .data_a_out_task(inj_data_a_out_task_1755007874206_760),
        .data_b_out_task(inj_data_b_out_task_1755007874206_268),
        .arg_in_task(inj_arg_in_task_1755007874206_869)
    );
    mod_unused_ports mod_unused_ports_inst_1755007874206_2775 (
        .unused_in(reset),
        .unused_out(inj_unused_out_1755007874206_212)
    );
    and a1 (inj_g_out_and_1755007874206_2, clk, clk);
    or  o1 (inj_g_out_or_1755007874206_780 , clk, clk);
    // END: Module_GatePrimitives_ts1755007874206
endmodule

