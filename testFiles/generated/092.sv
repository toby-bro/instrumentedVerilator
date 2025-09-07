module mod_split_nested (
    input logic clk,
    input logic cond1,
    input logic cond2,
    input logic [7:0] data_in,
    input logic reset,
    output logic [7:0] out_nested_a,
    output logic [7:0] out_nested_b
);
    logic [7:0]  split_nested_var;
    logic [7:0] other_nested_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_nested_var <= 8'b0;
            other_nested_var <= 8'b0;
        end else begin
            split_nested_var <= 8'h11; 
            other_nested_var <= 8'h22; 
            if (cond1) begin
                split_nested_var <= data_in + 10;
                other_nested_var <= data_in + 20;
                if (cond2) begin
                    split_nested_var <= data_in + 100;
                    other_nested_var <= data_in + 200;
                end
            end else begin
                split_nested_var <= data_in - 10;
                other_nested_var <= data_in - 20;
            end
        end
    end
    always_comb begin
        out_nested_a = split_nested_var;
        out_nested_b = other_nested_var;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_bind_in_1755007783225_713,
    input logic inj_cond2_1755007783233_813,
    input logic [3:0] inj_data0_1755007783224_747,
    input logic [3:0] inj_data1_1755007783224_937,
    input logic [3:0] inj_data2_1755007783224_465,
    input logic [3:0] inj_data3_1755007783224_139,
    input int inj_diag_input_val_1755007783223_524,
    input logic [7:0] inj_in_data_1755007783221_627,
    input logic [15:0] inj_in_vector_1755007783228_952,
    input logic [4:0] inj_index_1755007783221_894,
    input logic [1:0] inj_sel_in_1755007783224_280,
    input wire reset,
    output logic inj_bind_out_1755007783225_257,
    output logic [3:0] inj_data_out_case_1755007783224_29,
    output bit inj_diag_output_flag_1755007783223_616,
    output logic [7:0] inj_final_result_1755007783221_754,
    output logic [7:0] inj_out_data_1755007783221_705,
    output logic [7:0] inj_out_nested_a_1755007783233_733,
    output logic [7:0] inj_out_nested_b_1755007783233_945,
    output reg inj_out_res_1755007783226_754,
    output logic [7:0] inj_out_slice_1755007783228_706,
    output logic inj_single_out_1755007783230_136
);
    // BEGIN: SimpleAssign_ts1755007783221
    // BEGIN: dup_literal_param_ts1755007783222
    parameter CONST_A = 8'd10;
    localparam CONST_B = 8'd20;
    parameter CONST_C = 10;
    localparam CONST_D = 8'hFF;
    parameter CONST_E = 8'b01010101;
    logic [7:0] temp1_ts1755007783222, temp2_ts1755007783222;
    assign temp1_ts1755007783222 = inj_index_1755007783221_894 + CONST_A;
    assign temp2_ts1755007783222 = inj_index_1755007783221_894 + 10;
    always_comb begin
        logic [7:0] local_temp_ts1755007783222;
            mod_split_nested mod_split_nested_inst_1755007783233_968 (
                .data_in(temp2_ts1755007783222),
                .reset(reset),
                .out_nested_a(inj_out_nested_a_1755007783233_733),
                .out_nested_b(inj_out_nested_b_1755007783233_945),
                .clk(clk),
                .cond1(inj_bind_in_1755007783225_713),
                .cond2(inj_cond2_1755007783233_813)
            );
            // BEGIN: multi_port_decl_module_ts1755007783230
            always_comb begin
                inj_single_out_1755007783230_136 = inj_bind_in_1755007783225_713;
            end
            // END: multi_port_decl_module_ts1755007783230

            // BEGIN: MiscExpressions_ValueRange_ts1755007783228
            always_comb begin
                inj_out_slice_1755007783228_706 = inj_in_vector_1755007783228_952[7:0];
            end
            // END: MiscExpressions_ValueRange_ts1755007783228

            // BEGIN: case_default_ts1755007783226
            always_comb begin
                inj_out_res_1755007783226_754 = 1'b0;
                case (inj_sel_in_1755007783224_280)
                    2'b01: inj_out_res_1755007783226_754 = 1'b1;
                    2'b10: inj_out_res_1755007783226_754 = 1'b0;
                    default: inj_out_res_1755007783226_754 = 1'b1;
                endcase
            end
            // END: case_default_ts1755007783226

            // BEGIN: bind_module_ts1755007783225
            assign inj_bind_out_1755007783225_257 = inj_bind_in_1755007783225_713;
            // END: bind_module_ts1755007783225

            // BEGIN: case_selector_ts1755007783224
            always_comb begin
                case (inj_sel_in_1755007783224_280)
                    2'b00: inj_data_out_case_1755007783224_29 = inj_data0_1755007783224_747; 
                    2'b01: inj_data_out_case_1755007783224_29 = inj_data1_1755007783224_937; 
                    2'b10: inj_data_out_case_1755007783224_29 = inj_data2_1755007783224_465; 
                    default: inj_data_out_case_1755007783224_29 = inj_data3_1755007783224_139; 
                endcase
            end
            // END: case_selector_ts1755007783224

            // BEGIN: PragmaDiagnosticDirective_ts1755007783223
        `ifdef SLANG_PRAGMA
        `diagnostic push
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic ignore "SLANG_UNUSED_VARIABLE"
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic warn "SLANG_IMPLICIT_CAST"
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic error "SLANG_MULTIPLE_DRIVER"
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic fatal "SLANG_SYNTAX_ERROR_FATAL"
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic ignore (value=("SLANG_UNDRIVEN_SIGNAL", "SLANG_UNREAD_SIGNAL"))
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic warn (value="SLANG_LATCH_INFERRED")
        `endif
        assign inj_diag_output_flag_1755007783223_616 = (inj_diag_input_val_1755007783223_524 > 0);
        `ifdef SLANG_PRAGMA
        `diagnostic pop
        `endif
            // END: PragmaDiagnosticDirective_ts1755007783223

        local_temp_ts1755007783222 = inj_index_1755007783221_894 * CONST_B;
        inj_final_result_1755007783221_754 = temp1_ts1755007783222 + temp2_ts1755007783222 + local_temp_ts1755007783222;
        if (inj_index_1755007783221_894 > 5) begin
            inj_final_result_1755007783221_754 = inj_final_result_1755007783221_754 + 1;
        end else if (inj_index_1755007783221_894 < CONST_C) begin
            inj_final_result_1755007783221_754 = inj_final_result_1755007783221_754 - 1;
        end
        case (inj_index_1755007783221_894)
            5'd0: inj_final_result_1755007783221_754 = CONST_A;
            5'd1: inj_final_result_1755007783221_754 = 20;
            5'd2: inj_final_result_1755007783221_754 = 10;
            5'd3: inj_final_result_1755007783221_754 = CONST_B;
            5'd4: inj_final_result_1755007783221_754 = CONST_D;
            5'd5: inj_final_result_1755007783221_754 = 8'hFF;
            default: inj_final_result_1755007783221_754 = CONST_E;
        endcase
    end
    // END: dup_literal_param_ts1755007783222

    assign inj_out_data_1755007783221_705 = inj_in_data_1755007783221_627;
    // END: SimpleAssign_ts1755007783221
endmodule

