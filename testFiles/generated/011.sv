module bitwise_ops (
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [7:0] in3,
    output logic [7:0] out
);
    assign out = (in1 & in2) | (~in3) ^ (in1 << 2) >> 1;
endmodule

module module_ternary (
    input wire in_cond_ternary,
    input wire [7:0] in_val1,
    input wire [7:0] in_val2,
    output logic [7:0] out_ternary_result
);
    always_comb begin
    out_ternary_result = in_cond_ternary ? in_val1 : in_val2;
    end
endmodule

module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007753916_498,
    input logic [3:0] inj_case_inside_val_1755007753916_507,
    input logic inj_data_in_1755007753919_194,
    input logic inj_enable_in_1755007753919_82,
    input logic [7:0] inj_in1_1755007753917_981,
    input logic [7:0] inj_in2_1755007753917_706,
    input logic [7:0] inj_in3_1755007753917_680,
    input wire [7:0] inj_in_val1_1755007753917_832,
    input wire [7:0] inj_in_val2_1755007753917_820,
    input wire reset,
    output logic [3:0] inj_data_out1_n_1755007753917_80,
    output logic [3:0] inj_data_out2_n_1755007753917_0,
    output logic inj_data_out_1755007753919_946,
    output logic [4:0] inj_internal_out_1755007753916_802,
    output logic [7:0] inj_out_1755007753917_725,
    output logic [7:0] inj_out_1755007753918_788,
    output logic inj_out_1755007753920_121,
    output logic [7:0] inj_out_ternary_result_1755007753917_2
);
    // BEGIN: case_unique_casez_reordered_mod_ts1755007753916
    // BEGIN: split_multiple_blocking_ts1755007753917
    logic [3:0] temp_n_ts1755007753917;
        // BEGIN: mod_always_event_ts1755007753920
        always @(posedge clk or negedge reset) begin
            if (!reset) begin
                inj_out_1755007753920_121 <= 1'b0;
            end else begin
                inj_out_1755007753920_121 <= inj_enable_in_1755007753919_82;
            end
        end
        // END: mod_always_event_ts1755007753920

        // BEGIN: sequential_register_ts1755007753919
        always_ff @(posedge clk or negedge reset) begin
            if (!reset) begin
                inj_data_out_1755007753919_946 <= 1'b0; 
            end else if (inj_enable_in_1755007753919_82) begin
                inj_data_out_1755007753919_946 <= inj_data_in_1755007753919_194; 
            end
        end
        // END: sequential_register_ts1755007753919

        // BEGIN: timed_assign_unhandled_ts1755007753918
        always @(posedge clk) begin
            inj_out_1755007753918_788 <= inj_in1_1755007753917_981;
        end
        // END: timed_assign_unhandled_ts1755007753918

    always @(*) begin
        temp_n_ts1755007753917 = inj_case_inside_val_1755007753916_507 + 1;
        inj_data_out1_n_1755007753917_80 = temp_n_ts1755007753917 * 2;
        inj_data_out2_n_1755007753917_0 = temp_n_ts1755007753917 + 3;
    end
    // END: split_multiple_blocking_ts1755007753917

    bitwise_ops bitwise_ops_inst_1755007753917_4899 (
        .in3(inj_in3_1755007753917_680),
        .out(inj_out_1755007753917_725),
        .in1(inj_in1_1755007753917_981),
        .in2(inj_in2_1755007753917_706)
    );
    module_ternary module_ternary_inst_1755007753917_7465 (
        .in_cond_ternary(clk),
        .in_val1(inj_in_val1_1755007753917_832),
        .in_val2(inj_in_val2_1755007753917_820),
        .out_ternary_result(inj_out_ternary_result_1755007753917_2)
    );
    always @* begin
        unique casez ({inj_case_expr_1755007753916_498[0], inj_case_inside_val_1755007753916_507[3:2], inj_case_expr_1755007753916_498[1]})
            4'b1?0?: inj_internal_out_1755007753916_802 = 30;
            4'b?101: inj_internal_out_1755007753916_802 = 31;  
            4'b0?1?: inj_internal_out_1755007753916_802 = 32;
            4'b1?1?: inj_internal_out_1755007753916_802 = 33;  
            4'b?111: inj_internal_out_1755007753916_802 = 34;  
        endcase
    end
    // END: case_unique_casez_reordered_mod_ts1755007753916
endmodule

