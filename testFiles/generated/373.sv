module snippet (
    input wire clk,
    input logic [3:0] inj_case_inside_val_1755007879335_726,
    input logic [7:0] inj_data_1755007879333_575,
    input logic [7:0] inj_i2_s_1755007879334_60,
    input logic [7:0] inj_i3_s_1755007879334_247,
    input logic [2:0] inj_shift_val_1755007879333_35,
    input logic inj_start_task_1755007879337_821,
    input wire reset,
    output logic [7:0] inj_data_a_out_task_1755007879337_918,
    output logic [7:0] inj_data_b_out_task_1755007879337_726,
    output logic [4:0] inj_internal_out_1755007879335_839,
    output logic [7:0] inj_left_shift_log_1755007879333_781,
    output logic [7:0] inj_o1_s_1755007879334_37,
    output logic [7:0] inj_o2_s_1755007879334_669,
    output logic [7:0] inj_o3_s_1755007879334_378,
    output logic inj_out_o_1755007879336_317,
    output logic [7:0] inj_right_shift_arith_1755007879333_68,
    output logic [7:0] inj_right_shift_log_1755007879333_990
);
    // BEGIN: ShiftOperations_ts1755007879334
    // BEGIN: split_complex_nb_ts1755007879334
    logic [7:0] t1_s_ts1755007879334, t2_s_ts1755007879334;
        // BEGIN: module_task_args_ts1755007879338
        logic [7:0] data_a_ts1755007879338 ;
        logic [7:0] data_b_ts1755007879338 ;
        task automatic modify_vars;
            input logic [7:0] task_arg_ts1755007879338;
            logic [7:0] task_local_ts1755007879338 ;
            begin
                task_local_ts1755007879338 = task_arg_ts1755007879338;
                data_a_ts1755007879338 = task_local_ts1755007879338 + 8'd1;
                data_b_ts1755007879338 = task_arg_ts1755007879338 - 8'd1;
            end
        endtask
        always_comb begin
            if (inj_start_task_1755007879337_821) begin
                data_a_ts1755007879338 = t2_s_ts1755007879334;
                data_b_ts1755007879338 = 8'hFF;
                modify_vars(t1_s_ts1755007879334);
            end else begin
                data_a_ts1755007879338 = 8'h00;
                data_b_ts1755007879338 = 8'h00;
            end
        end
        always_comb begin
            inj_data_a_out_task_1755007879337_918 = data_a_ts1755007879338 + 8'd2;
            inj_data_b_out_task_1755007879337_726 = data_b_ts1755007879338;
        end
        // END: module_task_args_ts1755007879338

        // BEGIN: mod_internal_if_test_ts1755007879336
        assign inj_out_o_1755007879336_317 = !clk;
        // END: mod_internal_if_test_ts1755007879336

        // BEGIN: case_parallel_simple_mod_ts1755007879335
        always @* begin
            (* parallel *)
            case (inj_case_inside_val_1755007879335_726)
                4'd0, 4'd1: inj_internal_out_1755007879335_839 = 14;
                4'd2, 4'd3: inj_internal_out_1755007879335_839 = 15;
                default: inj_internal_out_1755007879335_839 = 18;
            endcase
        end
        // END: case_parallel_simple_mod_ts1755007879335

    always @(posedge clk) begin
        t1_s_ts1755007879334 <= inj_data_1755007879333_575 + inj_i2_s_1755007879334_60;
        inj_o1_s_1755007879334_37 <= t1_s_ts1755007879334 - inj_i3_s_1755007879334_247;
        t2_s_ts1755007879334 <= inj_i2_s_1755007879334_60 * inj_i3_s_1755007879334_247;
        inj_o2_s_1755007879334_669 <= t1_s_ts1755007879334 + t2_s_ts1755007879334;
        inj_o3_s_1755007879334_378 <= t2_s_ts1755007879334 / 2;
    end
    // END: split_complex_nb_ts1755007879334

    assign inj_left_shift_log_1755007879333_781 = inj_data_1755007879333_575 << inj_shift_val_1755007879333_35;
    assign inj_right_shift_log_1755007879333_990 = inj_data_1755007879333_575 >> inj_shift_val_1755007879333_35;
    assign inj_right_shift_arith_1755007879333_68 = $signed(inj_data_1755007879333_575) >>> inj_shift_val_1755007879333_35;
    // END: ShiftOperations_ts1755007879334
endmodule

