module CaseEq (
    output wire match_x_neq,
    output wire match_z_eq,
    inout wire [3:0] data_io
);
    assign match_z_eq = (data_io === 4'b101z);
    assign match_x_neq = (data_io !== 4'b1x0x);
endmodule

module undeclared_but_found_pkg_diag_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module snippet (
    input wire clk,
    input logic inj_a_1755007799192_15,
    input logic inj_b_1755007799192_512,
    input logic [1:0] inj_case_expr_1755007799195_186,
    input bit inj_enable_crypto_1755007799191_442,
    input int inj_in_val_1755007799194_235,
    input logic [4:0] inj_index_1755007799192_556,
    input wire reset,
    output bit inj_crypto_active_1755007799191_652,
    output logic inj_dummy_1755007799192_607,
    output logic [7:0] inj_final_result_1755007799192_805,
    output logic [4:0] inj_internal_out_1755007799195_196,
    output wire inj_match_x_neq_1755007799196_252,
    output wire inj_match_z_eq_1755007799196_26,
    output wire inj_out_1755007799192_387,
    output int inj_out_val_1755007799194_375,
    output logic [7:0] inj_out_vec_1755007799197_532,
    output logic inj_sum_1755007799192_546,
    inout wire [3:0] inj_data_io_1755007799196_35
);
    // BEGIN: PragmaProtectKeyBlock_ts1755007799192
`ifdef SLANG_PRAGMA
`protect key
`endif
`ifdef SLANG_PRAGMA
`protect block
`endif
    // BEGIN: mod_err_event_constant_ts1755007799192
    // BEGIN: simple_adder_ts1755007799192
    // BEGIN: Comb_Assign_ts1755007799192
    // BEGIN: dup_literal_param_ts1755007799193
    parameter CONST_A = 8'd10;
    localparam CONST_B = 8'd20;
    parameter CONST_C = 10;
    localparam CONST_D = 8'hFF;
    parameter CONST_E = 8'b01010101;
    logic [7:0] temp1_ts1755007799193, temp2_ts1755007799193;
    assign temp1_ts1755007799193 = inj_index_1755007799192_556 + CONST_A;
    assign temp2_ts1755007799193 = inj_index_1755007799192_556 + 10;
    always_comb begin
        logic [7:0] local_temp_ts1755007799193;
            // BEGIN: SimpleLoopExample_ts1755007799197
            always_comb begin
                for (int i = 0; i < 8; i++) begin
                    inj_out_vec_1755007799197_532[i] = temp2_ts1755007799193[7 - i];
                end
            end
            // END: SimpleLoopExample_ts1755007799197

            CaseEq CaseEq_inst_1755007799196_7497 (
                .match_x_neq(inj_match_x_neq_1755007799196_252),
                .match_z_eq(inj_match_z_eq_1755007799196_26),
                .data_io(inj_data_io_1755007799196_35)
            );
            // BEGIN: case_unique0_violating_mod_ts1755007799195
            always @* begin
                unique0 casez (inj_case_expr_1755007799195_186)
                    2'b1?: inj_internal_out_1755007799195_196 = 8;
                    2'b11: inj_internal_out_1755007799195_196 = 9;  
                    2'b?1: inj_internal_out_1755007799195_196 = 10; 
                    2'b00: inj_internal_out_1755007799195_196 = 11; 
                endcase
            end
            // END: case_unique0_violating_mod_ts1755007799195

            undeclared_but_found_pkg_diag_mod undeclared_but_found_pkg_diag_mod_inst_1755007799194_2987 (
                .in_val(inj_in_val_1755007799194_235),
                .out_val(inj_out_val_1755007799194_375)
            );
        local_temp_ts1755007799193 = inj_index_1755007799192_556 * CONST_B;
        inj_final_result_1755007799192_805 = temp1_ts1755007799193 + temp2_ts1755007799193 + local_temp_ts1755007799193;
        if (inj_index_1755007799192_556 > 5) begin
            inj_final_result_1755007799192_805 = inj_final_result_1755007799192_805 + 1;
        end else if (inj_index_1755007799192_556 < CONST_C) begin
            inj_final_result_1755007799192_805 = inj_final_result_1755007799192_805 - 1;
        end
        case (inj_index_1755007799192_556)
            5'd0: inj_final_result_1755007799192_805 = CONST_A;
            5'd1: inj_final_result_1755007799192_805 = 20;
            5'd2: inj_final_result_1755007799192_805 = 10;
            5'd3: inj_final_result_1755007799192_805 = CONST_B;
            5'd4: inj_final_result_1755007799192_805 = CONST_D;
            5'd5: inj_final_result_1755007799192_805 = 8'hFF;
            default: inj_final_result_1755007799192_805 = CONST_E;
        endcase
    end
    // END: dup_literal_param_ts1755007799193

    assign inj_out_1755007799192_387 = reset & clk;
    // END: Comb_Assign_ts1755007799192

    assign inj_sum_1755007799192_546 = inj_a_1755007799192_15 + inj_b_1755007799192_512;
    // END: simple_adder_ts1755007799192

    always @(posedge 1'b1) begin
        inj_dummy_1755007799192_607 = ~inj_dummy_1755007799192_607;
    end
    // END: mod_err_event_constant_ts1755007799192

assign inj_crypto_active_1755007799191_652 = inj_enable_crypto_1755007799191_442;
    // END: PragmaProtectKeyBlock_ts1755007799192
endmodule

