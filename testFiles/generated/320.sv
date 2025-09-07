module PragmaDiagnosticDirective (
    input int diag_input_val,
    output bit diag_output_flag
);
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
assign diag_output_flag = (diag_input_val > 0);
`ifdef SLANG_PRAGMA
`diagnostic pop
`endif
endmodule

module dup_literal_param (
    input logic [4:0] index,
    output logic [7:0] final_result
);
    parameter CONST_A = 8'd10;
    localparam CONST_B = 8'd20;
    parameter CONST_C = 10;
    localparam CONST_D = 8'hFF;
    parameter CONST_E = 8'b01010101;
    logic [7:0] temp1, temp2;
    assign temp1 = index + CONST_A;
    assign temp2 = index + 10;
    always_comb begin
        logic [7:0] local_temp;
        local_temp = index * CONST_B;
        final_result = temp1 + temp2 + local_temp;
        if (index > 5) begin
            final_result = final_result + 1;
        end else if (index < CONST_C) begin
            final_result = final_result - 1;
        end
        case (index)
            5'd0: final_result = CONST_A;
            5'd1: final_result = 20;
            5'd2: final_result = 10;
            5'd3: final_result = CONST_B;
            5'd4: final_result = CONST_D;
            5'd5: final_result = 8'hFF;
            default: final_result = CONST_E;
        endcase
    end
endmodule

module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
endmodule

module reduction_ops (
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic out
);
    assign out = &in1 | ^in2;
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
    input int inj_diag_input_val_1755007861918_499,
    input logic [3:0] inj_i_control_1755007861920_485,
    input logic [7:0] inj_in1_1755007861919_157,
    input logic [7:0] inj_in2_1755007861919_874,
    input logic [4:0] inj_index_1755007861922_512,
    input logic [15:0] inj_packed_in_1755007861919_457,
    input logic inj_unused_in_1755007861919_382,
    input wire reset,
    output bit inj_diag_output_flag_1755007861918_342,
    output logic [7:0] inj_field0_byte_o_1755007861919_996,
    output logic [7:0] inj_final_result_1755007861922_835,
    output wire inj_o_c_1755007861924_584,
    output logic [7:0] inj_o_result_1755007861920_889,
    output logic inj_o_status_1755007861920_453,
    output logic [7:0] inj_out2_a_1755007861922_169,
    output logic inj_out_1755007861919_305,
    output logic inj_out_1755007861921_462,
    output logic inj_out_b_1755007861919_689,
    output logic [7:0] inj_out_x_j_1755007861923_353,
    output logic [7:0] inj_out_y_j_1755007861923_343,
    output logic inj_unused_out_1755007861919_778
);
    // BEGIN: unreferenced_module_ts1755007861919
    // BEGIN: LintUnusedSignal_ts1755007861919
    logic unused_w_ts1755007861919; 
        // BEGIN: module_simple_ts1755007861924
        wire internal_xor_res_ts1755007861924;
        assign internal_xor_res_ts1755007861924 = reset ^ clk;
        assign inj_o_c_1755007861924_584 = internal_xor_res_ts1755007861924 & reset;
        // END: module_simple_ts1755007861924

        // BEGIN: split_multiple_in_branch_ts1755007861923
        always @(posedge clk) begin
            if (unused_w_ts1755007861919) begin
                inj_out_x_j_1755007861923_353 <= inj_in1_1755007861919_157 * 3;
                inj_out_y_j_1755007861923_343 <= inj_in2_1755007861919_874 + 1;
            end else begin
                inj_out_x_j_1755007861923_353 <= inj_in1_1755007861919_157;
                inj_out_y_j_1755007861923_343 <= inj_in2_1755007861919_874;
            end
        end
        // END: split_multiple_in_branch_ts1755007861923

        // BEGIN: split_basic_nonblocking_ts1755007861922
        always @(posedge clk) begin
            inj_out2_a_1755007861922_169 <= inj_in1_1755007861919_157;
        end
        // END: split_basic_nonblocking_ts1755007861922

        dup_literal_param dup_literal_param_inst_1755007861922_8275 (
            .final_result(inj_final_result_1755007861922_835),
            .index(inj_index_1755007861922_512)
        );
        // BEGIN: simple_and_gate_ts1755007861921
        assign inj_out_1755007861921_462 = inj_unused_in_1755007861919_382 & unused_w_ts1755007861919;
        // END: simple_and_gate_ts1755007861921

        // BEGIN: bind_directive_top_ts1755007861920
        target_module_for_bind target_inst(
            .i_target_clk   (clk),
            .i_target_data  (inj_in2_1755007861919_874),
            .o_target_result(inj_o_result_1755007861920_889)
        );
        module_to_bind bind_inst(
            .i_bind_clk     (clk),
            .i_bind_control (inj_i_control_1755007861920_485),
            .o_bind_status  (inj_o_status_1755007861920_453)
        );
        // END: bind_directive_top_ts1755007861920

        reduction_ops reduction_ops_inst_1755007861919_7445 (
            .in2(inj_in2_1755007861919_874),
            .out(inj_out_1755007861919_305),
            .in1(inj_in1_1755007861919_157)
        );
        // BEGIN: typedef_union_mod_ts1755007861919
        typedef union packed {
            logic [15:0] word_ts1755007861919;
            logic [1:0][7:0] byte_fields_ts1755007861919;
        } my_packed_union_t;
        my_packed_union_t my_union_var;
        always_comb begin
            my_union_var.word_ts1755007861919 = inj_packed_in_1755007861919_457;
        end
        assign inj_field0_byte_o_1755007861919_996 = my_union_var.byte_fields_ts1755007861919[0];
        // END: typedef_union_mod_ts1755007861919

    assign inj_out_b_1755007861919_689 = inj_unused_in_1755007861919_382;
    // END: LintUnusedSignal_ts1755007861919

    assign inj_unused_out_1755007861919_778 = ~inj_unused_in_1755007861919_382;
    // END: unreferenced_module_ts1755007861919

    PragmaDiagnosticDirective PragmaDiagnosticDirective_inst_1755007861918_4328 (
        .diag_output_flag(inj_diag_output_flag_1755007861918_342),
        .diag_input_val(inj_diag_input_val_1755007861918_499)
    );
endmodule

