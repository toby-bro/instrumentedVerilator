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

module snippet #(
    parameter integer DATA_WIDTH = 8
) (
    input wire clk,
    input wire [3:0] inj_dffcl_ctrl_mode_1755007884958_659,
    input wire [15:0] inj_dffcl_data_in1_1755007884958_752,
    input wire [15:0] inj_dffcl_data_in2_1755007884958_233,
    input bit inj_dummy_in_1755007884958_430,
    input logic [7:0] inj_in_a_1755007884958_310,
    input logic [7:0] inj_in_b_1755007884958_717,
    input wire [7:0] inj_param_in_1755007884958_825,
    input logic inj_start_task_1755007884958_573,
    input wire reset,
    output logic [7:0] inj_data_a_out_task_1755007884958_32,
    output logic [7:0] inj_data_b_out_task_1755007884958_785,
    output logic [15:0] inj_dffcl_data_out_1755007884958_444,
    output bit inj_dummy_out_1755007884958_710,
    output logic [15:0] inj_out_concat_1755007884958_743,
    output wire [7:0] inj_param_out_1755007884958_674
);
    // BEGIN: ComplexConversions_ts1755007884958
    // BEGIN: module_finish_numbers_ts1755007884958
    parameter p_finish_0 = 0;
    parameter p_finish_1 = 1;
    parameter p_finish_2 = 2;
    parameter p_finish_other_3 = 3;
    parameter p_finish_large_100 = 100;
    parameter p_finish_neg_minus1 = -1;
    localparam lp_finish_0 = 0;
    localparam lp_finish_1 = 1;
    localparam lp_finish_2 = 2;
    localparam lp_finish_other_5 = 5;
    localparam lp_finish_neg_minus10 = -10;
    // BEGIN: deep_ff_control_logic_ts1755007884959
    always_ff @(posedge clk or negedge reset) begin
    if (!reset) begin
        inj_dffcl_data_out_1755007884958_444 <= 16'h0000;
    end else begin
        case (inj_dffcl_ctrl_mode_1755007884958_659)
            4'd0: inj_dffcl_data_out_1755007884958_444 <= inj_dffcl_data_in1_1755007884958_752 + inj_dffcl_data_in2_1755007884958_233;
            4'd1: begin
                if (inj_dffcl_data_in1_1755007884958_752 > inj_dffcl_data_in2_1755007884958_233) begin
                    case (inj_dffcl_ctrl_mode_1755007884958_659[1:0])
                        2'b00: inj_dffcl_data_out_1755007884958_444 <= inj_dffcl_data_in1_1755007884958_752 - inj_dffcl_data_in2_1755007884958_233;
                        2'b01: inj_dffcl_data_out_1755007884958_444 <= inj_dffcl_data_in1_1755007884958_752 & inj_dffcl_data_in2_1755007884958_233;
                        default: inj_dffcl_data_out_1755007884958_444 <= inj_dffcl_data_in1_1755007884958_752 | inj_dffcl_data_in2_1755007884958_233;
                    endcase
                end else begin
                    case (inj_dffcl_ctrl_mode_1755007884958_659[1:0])
                        2'b00: inj_dffcl_data_out_1755007884958_444 <= inj_dffcl_data_in2_1755007884958_233 - inj_dffcl_data_in1_1755007884958_752;
                        2'b01: inj_dffcl_data_out_1755007884958_444 <= inj_dffcl_data_in1_1755007884958_752 ^ inj_dffcl_data_in2_1755007884958_233;
                        default: inj_dffcl_data_out_1755007884958_444 <= ~inj_dffcl_data_in1_1755007884958_752;
                    endcase
                end
            end
            4'd2: begin
                casez (inj_dffcl_data_in1_1755007884958_752[15:13])
                    3'b000: inj_dffcl_data_out_1755007884958_444 <= inj_dffcl_data_in2_1755007884958_233;
                    3'b001: inj_dffcl_data_out_1755007884958_444 <= ~inj_dffcl_data_in2_1755007884958_233;
                    3'b01?: begin
                        if (inj_dffcl_data_in2_1755007884958_233[0]) inj_dffcl_data_out_1755007884958_444 <= inj_dffcl_data_in1_1755007884958_752 << 1;
                        else inj_dffcl_data_out_1755007884958_444 <= inj_dffcl_data_in1_1755007884958_752 >> 1;
                    end
                    3'b1??: begin
                        if (inj_dffcl_ctrl_mode_1755007884958_659[0]) inj_dffcl_data_out_1755007884958_444 <= inj_dffcl_data_in1_1755007884958_752 + 1;
                        else inj_dffcl_data_out_1755007884958_444 <= inj_dffcl_data_in1_1755007884958_752 - 1;
                    end
                    default: inj_dffcl_data_out_1755007884958_444 <= 16'hAAAA;
                endcase
            end
            default: begin
                if (inj_dffcl_ctrl_mode_1755007884958_659[2]) inj_dffcl_data_out_1755007884958_444 <= inj_dffcl_data_in1_1755007884958_752;
                else inj_dffcl_data_out_1755007884958_444 <= inj_dffcl_data_in2_1755007884958_233;
            end
        endcase
    end
    end
    // END: deep_ff_control_logic_ts1755007884959

    // BEGIN: module_with_params_ts1755007884958
    assign inj_param_out_1755007884958_674 = inj_param_in_1755007884958_825;
    // END: module_with_params_ts1755007884958

    module_task_args module_task_args_inst_1755007884958_5721 (
        .data_a_init_task(inj_in_b_1755007884958_717),
        .start_task(inj_start_task_1755007884958_573),
        .data_a_out_task(inj_data_a_out_task_1755007884958_32),
        .data_b_out_task(inj_data_b_out_task_1755007884958_785),
        .arg_in_task(inj_in_a_1755007884958_310)
    );
    assign inj_dummy_out_1755007884958_710 = inj_dummy_in_1755007884958_430;
    // END: module_finish_numbers_ts1755007884958

    always_comb begin
        inj_out_concat_1755007884958_743 = {inj_in_a_1755007884958_310, inj_in_b_1755007884958_717};
    end
    // END: ComplexConversions_ts1755007884958
endmodule

