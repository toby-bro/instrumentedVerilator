module snippet (
    input wire clk,
    input logic [7:0] inj_arg_in_task_1755007881417_837,
    input logic [7:0] inj_data_a_init_task_1755007881417_476,
    input logic inj_start_task_1755007881417_678,
    input wire reset,
    output logic [7:0] inj_data_a_out_task_1755007881417_226,
    output logic [7:0] inj_data_b_out_task_1755007881417_879
);
    // BEGIN: module_task_args_ts1755007881418
    logic [7:0] data_a_ts1755007881418 ;
    logic [7:0] data_b_ts1755007881418 ;
    task automatic modify_vars;
        input logic [7:0] task_arg_ts1755007881418;
        logic [7:0] task_local_ts1755007881418 ;
        begin
            task_local_ts1755007881418 = task_arg_ts1755007881418;
            data_a_ts1755007881418 = task_local_ts1755007881418 + 8'd1;
            data_b_ts1755007881418 = task_arg_ts1755007881418 - 8'd1;
        end
    endtask
    always_comb begin
        if (inj_start_task_1755007881417_678) begin
            data_a_ts1755007881418 = inj_data_a_init_task_1755007881417_476;
            data_b_ts1755007881418 = 8'hFF;
            modify_vars(inj_arg_in_task_1755007881417_837);
        end else begin
            data_a_ts1755007881418 = 8'h00;
            data_b_ts1755007881418 = 8'h00;
        end
    end
    always_comb begin
        inj_data_a_out_task_1755007881417_226 = data_a_ts1755007881418 + 8'd2;
        inj_data_b_out_task_1755007881417_879 = data_b_ts1755007881418;
    end
    // END: module_task_args_ts1755007881418
endmodule

