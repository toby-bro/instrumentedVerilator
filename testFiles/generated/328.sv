module snippet (
    input wire clk,
    input logic [7:0] inj_arg_in_task_1755007864478_902,
    input logic [7:0] inj_data_a_init_task_1755007864478_831,
    input bit [7:0] inj_in_cmd_1755007864478_667,
    input bit [3:0] inj_in_data_1755007864478_485,
    input logic inj_start_task_1755007864478_47,
    input wire reset,
    output logic [7:0] inj_data_a_out_task_1755007864478_652,
    output logic [7:0] inj_data_b_out_task_1755007864478_573,
    output logic [7:0] inj_out1_f_1755007864479_251,
    output logic [7:0] inj_out2_f_1755007864479_888,
    output logic [7:0] inj_out3_f_1755007864479_896,
    output bit [3:0] inj_out_result_1755007864478_933,
    output bit [3:0] inj_out_status_1755007864478_58
);
    // BEGIN: mod_if_else_simple_ts1755007864478
    // BEGIN: module_task_args_ts1755007864478
    logic [7:0] data_a_ts1755007864478 ;
    logic [7:0] data_b_ts1755007864478 ;
        // BEGIN: split_independent_nb_ts1755007864479
        always @(posedge clk) begin
            inj_out1_f_1755007864479_251 <= inj_data_a_init_task_1755007864478_831;
            inj_out2_f_1755007864479_888 <= inj_arg_in_task_1755007864478_902;
            inj_out3_f_1755007864479_896 <= data_b_ts1755007864478;
        end
        // END: split_independent_nb_ts1755007864479

        // BEGIN: mod_case_standard_ts1755007864479
    always_comb begin
        case (inj_in_cmd_1755007864478_667)
            8'd0, 8'd1, 8'd2: begin
                inj_out_status_1755007864478_58 = 4'hA;
            end
            8'd3, 8'd4: begin
                inj_out_status_1755007864478_58 = 4'hB;
            end
            default: begin
                inj_out_status_1755007864478_58 = 4'hF;
            end
        endcase
    end
        // END: mod_case_standard_ts1755007864479

    task automatic modify_vars;
        input logic [7:0] task_arg_ts1755007864478;
        logic [7:0] task_local_ts1755007864478 ;
        begin
            task_local_ts1755007864478 = task_arg_ts1755007864478;
            data_a_ts1755007864478 = task_local_ts1755007864478 + 8'd1;
            data_b_ts1755007864478 = task_arg_ts1755007864478 - 8'd1;
        end
    endtask
    always_comb begin
        if (inj_start_task_1755007864478_47) begin
            data_a_ts1755007864478 = inj_data_a_init_task_1755007864478_831;
            data_b_ts1755007864478 = 8'hFF;
            modify_vars(inj_arg_in_task_1755007864478_902);
        end else begin
            data_a_ts1755007864478 = 8'h00;
            data_b_ts1755007864478 = 8'h00;
        end
    end
    always_comb begin
        inj_data_a_out_task_1755007864478_652 = data_a_ts1755007864478 + 8'd2;
        inj_data_b_out_task_1755007864478_573 = data_b_ts1755007864478;
    end
    // END: module_task_args_ts1755007864478

always_comb begin
    if (inj_in_data_1755007864478_485 > 8) begin
        inj_out_result_1755007864478_933 = inj_in_data_1755007864478_485 + 1;
    end else begin
        inj_out_result_1755007864478_933 = inj_in_data_1755007864478_485 - 1;
    end
end
    // END: mod_if_else_simple_ts1755007864478
endmodule

