module PragmaProtectKeyBlock (
    input bit enable_crypto,
    output bit crypto_active
);
`ifdef SLANG_PRAGMA
`protect key
`endif
`ifdef SLANG_PRAGMA
`protect block
`endif
assign crypto_active = enable_crypto;
endmodule

module func_macro_args (
    input int input_int,
    output int output_int
);
    `define ADD(a, b)       ((a) + (b))
    `define SUBTRACT(x, y)  ((x) - (y))
    localparam int P1_ADD = `ADD(10, 20);
    int p2_sub_var;
    always_comb begin
        p2_sub_var = `SUBTRACT(50, input_int);
    end
    assign output_int = P1_ADD + p2_sub_var;
endmodule

module name_conflict_example (
    input logic i_in,
    output logic o_out
);
    parameter int my_param = 5;
    logic my_var;
    always_comb my_var = i_in;
    assign o_out = i_in && (my_param == 5) && my_var;
endmodule

module variable_sel_mux (
    input logic [7:0] in,
    input logic [2:0] index,
    output logic out
);
    assign out = in[index];
endmodule

module snippet (
    input wire clk,
    input bit inj_enable_crypto_1755007803936_238,
    input logic inj_in1_1755007803932_42,
    input logic inj_in2_1755007803932_447,
    input logic [1:0] inj_in_val_1755007803933_516,
    input int inj_in_val_1755007803934_920,
    input logic [7:0] inj_in_val_m2_1755007803931_624,
    input logic [2:0] inj_index_1755007803932_510,
    input logic [7:0] inj_sub_val_m2_1755007803931_76,
    input wire reset,
    output bit inj_crypto_active_1755007803936_631,
    output logic inj_o_out_1755007803934_534,
    output logic inj_out_1755007803932_204,
    output logic inj_out_1755007803932_810,
    output logic [7:0] inj_out_diff_m2_1755007803931_568,
    output reg inj_out_res_1755007803933_752,
    output int inj_out_val_1755007803934_225,
    output int inj_output_int_1755007803935_56,
    output logic inj_reset_1755007803932_192,
    output logic [7:0] inj_var_out_m2_1755007803931_205
);
    // BEGIN: expr_postsub_comb_ts1755007803932
    logic [7:0] var_m2_ts1755007803932;
        // BEGIN: cu_timeunit_mod_ts1755007803932
        logic internal_sig_ts1755007803932;
            PragmaProtectKeyBlock PragmaProtectKeyBlock_inst_1755007803936_2028 (
                .enable_crypto(inj_enable_crypto_1755007803936_238),
                .crypto_active(inj_crypto_active_1755007803936_631)
            );
            func_macro_args func_macro_args_inst_1755007803935_2010 (
                .input_int(inj_in_val_1755007803934_920),
                .output_int(inj_output_int_1755007803935_56)
            );
            // BEGIN: unknown_class_pkg_diag_mod_ts1755007803934
            assign inj_out_val_1755007803934_225 = inj_in_val_1755007803934_920;
            // END: unknown_class_pkg_diag_mod_ts1755007803934

            name_conflict_example name_conflict_example_inst_1755007803934_8090 (
                .o_out(inj_o_out_1755007803934_534),
                .i_in(internal_sig_ts1755007803932)
            );
            // BEGIN: case_empty_statement_ts1755007803933
            always_comb begin
                inj_out_res_1755007803933_752 = 1'b0;
                case (inj_in_val_1755007803933_516)
                    2'b00: inj_out_res_1755007803933_752 = 1'b1;
                    2'b01: ;
                    2'b10: inj_out_res_1755007803933_752 = 1'b0;
                    default: inj_out_res_1755007803933_752 = 1'b1;
                endcase
            end
            // END: case_empty_statement_ts1755007803933

        always_ff @(posedge clk) begin
            inj_reset_1755007803932_192 <= 1'b0;
            internal_sig_ts1755007803932 = clk;
        end
        // END: cu_timeunit_mod_ts1755007803932

        variable_sel_mux variable_sel_mux_inst_1755007803932_9624 (
            .in(var_m2_ts1755007803932),
            .index(inj_index_1755007803932_510),
            .out(inj_out_1755007803932_204)
        );
        // BEGIN: simple_and_gate_ts1755007803932
        assign inj_out_1755007803932_810 = inj_in1_1755007803932_42 & inj_in2_1755007803932_447;
        // END: simple_and_gate_ts1755007803932

    always_comb begin
        var_m2_ts1755007803932 = inj_in_val_m2_1755007803931_624;
        inj_out_diff_m2_1755007803931_568 = (var_m2_ts1755007803932--) - inj_sub_val_m2_1755007803931_76;
        inj_var_out_m2_1755007803931_205 = var_m2_ts1755007803932;
    end
    // END: expr_postsub_comb_ts1755007803932
endmodule

