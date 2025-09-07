module module_in_program_ref (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module keyword_import_export (
    input wire clk,
    input logic [3:0] inj_data0_1755538557425_322,
    input logic [3:0] inj_data1_1755538557425_880,
    input logic [3:0] inj_data2_1755538557425_824,
    input logic [3:0] inj_data3_1755538557425_467,
    input logic [7:0] inj_in1_1755538557425_459,
    input logic inj_in1_1755538557426_179,
    input logic [7:0] inj_in2_1755538557425_902,
    input logic [7:0] inj_in3_1755538557425_126,
    input int inj_in_val_1755538557425_691,
    input logic [4:0] inj_index_1755538557426_50,
    input logic [1:0] inj_sel_in_1755538557425_80,
    input logic keyword_in,
    input wire rst,
    output logic [3:0] inj_data_out_case_1755538557425_0,
    output logic [7:0] inj_final_result_1755538557426_728,
    output logic [7:0] inj_out_1755538557425_352,
    output logic inj_out_1755538557426_213,
    output int inj_out_val_1755538557425_59,
    output int inj_out_val_1755538557426_653,
    output logic keyword_out
);
    // BEGIN: bitwise_ops_ts1755538557425
    // BEGIN: case_selector_ts1755538557425
    // BEGIN: simple_undeclared_mod_ts1755538557425
    // BEGIN: simple_xor_gate_ts1755538557426
    // BEGIN: dup_literal_param_ts1755538557427
    parameter CONST_A = 8'd10;
    localparam CONST_B = 8'd20;
    parameter CONST_C = 10;
    localparam CONST_D = 8'hFF;
    parameter CONST_E = 8'b01010101;
    logic [7:0] temp1_ts1755538557427, temp2_ts1755538557427;
    assign temp1_ts1755538557427 = inj_index_1755538557426_50 + CONST_A;
    assign temp2_ts1755538557427 = inj_index_1755538557426_50 + 10;
    always_comb begin
        logic [7:0] local_temp_ts1755538557427;
        local_temp_ts1755538557427 = inj_index_1755538557426_50 * CONST_B;
        inj_final_result_1755538557426_728 = temp1_ts1755538557427 + temp2_ts1755538557427 + local_temp_ts1755538557427;
        if (inj_index_1755538557426_50 > 5) begin
            inj_final_result_1755538557426_728 = inj_final_result_1755538557426_728 + 1;
        end else if (inj_index_1755538557426_50 < CONST_C) begin
            inj_final_result_1755538557426_728 = inj_final_result_1755538557426_728 - 1;
        end
        case (inj_index_1755538557426_50)
            5'd0: inj_final_result_1755538557426_728 = CONST_A;
            5'd1: inj_final_result_1755538557426_728 = 20;
            5'd2: inj_final_result_1755538557426_728 = 10;
            5'd3: inj_final_result_1755538557426_728 = CONST_B;
            5'd4: inj_final_result_1755538557426_728 = CONST_D;
            5'd5: inj_final_result_1755538557426_728 = 8'hFF;
            default: inj_final_result_1755538557426_728 = CONST_E;
        endcase
    end
    // END: dup_literal_param_ts1755538557427

    module_in_program_ref module_in_program_ref_inst_1755538557426_2275 (
        .in_val(inj_in_val_1755538557425_691),
        .out_val(inj_out_val_1755538557426_653)
    );
    assign inj_out_1755538557426_213 = inj_in1_1755538557426_179 ^ keyword_in;
    // END: simple_xor_gate_ts1755538557426

    assign inj_out_val_1755538557425_59 = inj_in_val_1755538557425_691;
    // END: simple_undeclared_mod_ts1755538557425

    always_comb begin
        case (inj_sel_in_1755538557425_80)
            2'b00: inj_data_out_case_1755538557425_0 = inj_data0_1755538557425_322; 
            2'b01: inj_data_out_case_1755538557425_0 = inj_data1_1755538557425_880; 
            2'b10: inj_data_out_case_1755538557425_0 = inj_data2_1755538557425_824; 
            default: inj_data_out_case_1755538557425_0 = inj_data3_1755538557425_467; 
        endcase
    end
    // END: case_selector_ts1755538557425

    assign inj_out_1755538557425_352 = (inj_in1_1755538557425_459 & inj_in2_1755538557425_902) | (~inj_in3_1755538557425_126) ^ (inj_in1_1755538557425_459 << 2) >> 1;
    // END: bitwise_ops_ts1755538557425

    assign keyword_out = keyword_in;
endmodule

