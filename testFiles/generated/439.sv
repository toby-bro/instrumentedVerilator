module explicit_non_ansi_decl_module (
    p_in,
    p_out
);
    input logic p_in;
    output wire p_out;
    assign p_out = p_in;
endmodule

module snippet (
    input wire clk,
    input logic inj_in_bit_1755007900942_996,
    input logic [3:0] inj_in_h_1755007900941_571,
    input logic [3:0] inj_in_l_1755007900941_630,
    input logic [2:0] inj_in_val_1755007900942_221,
    input logic [7:0] inj_in_val_1755007900943_503,
    input wire reset,
    output logic inj_out_bit_1755007900942_58,
    output logic [7:0] inj_out_c_1755007900941_356,
    output logic inj_out_o_1755007900942_475,
    output logic [3:0] inj_out_part_1755007900943_321,
    output logic [7:0] inj_out_reg_1755007900943_153,
    output reg inj_out_res_1755007900942_338,
    output wire inj_p_out_1755007900944_93
);
    // BEGIN: concat_op_ts1755007900942
    // BEGIN: casez_xz_ts1755007900942
    // BEGIN: recursive_macro_dummy_ts1755007900942
    `define RECURSIVE_TEST `RECURSIVE_TEST
    // BEGIN: mod_internal_if_test_ts1755007900942
    // BEGIN: module_assignments_in_loops_ts1755007900943
    localparam int PART_START = 4;
    localparam int PART_WIDTH = 4;
    logic [7:0] reg_var_ts1755007900943;
    logic [3:0] part_var_ts1755007900943;
        explicit_non_ansi_decl_module explicit_non_ansi_decl_module_inst_1755007900944_2531 (
            .p_in(inj_in_bit_1755007900942_996),
            .p_out(inj_p_out_1755007900944_93)
        );
    always_comb begin
        reg_var_ts1755007900943  = inj_in_val_1755007900943_503;
        part_var_ts1755007900943 = 4'h0;
        for (int i = 0; i < 4; i++) begin
            reg_var_ts1755007900943  = reg_var_ts1755007900943 + i;
            reg_var_ts1755007900943 += (i * 2);
            reg_var_ts1755007900943 <<= inj_in_val_1755007900942_221;
            reg_var_ts1755007900943[i % 8] = (reg_var_ts1755007900943[i % 8] == 1'b0);
            reg_var_ts1755007900943[PART_START +: PART_WIDTH] = i[3:0];
        end
        part_var_ts1755007900943 = reg_var_ts1755007900943[7:4];
    end
    assign inj_out_reg_1755007900943_153  = reg_var_ts1755007900943;
    assign inj_out_part_1755007900943_321 = part_var_ts1755007900943;
    // END: module_assignments_in_loops_ts1755007900943

    assign inj_out_o_1755007900942_475 = !clk;
    // END: mod_internal_if_test_ts1755007900942

    assign inj_out_bit_1755007900942_58 = inj_in_bit_1755007900942_996;
    // END: recursive_macro_dummy_ts1755007900942

    always_comb begin
        inj_out_res_1755007900942_338 = 1'b0;
        casez (inj_in_val_1755007900942_221)
            3'b1??: inj_out_res_1755007900942_338 = 1'b1;
            3'b0z?: inj_out_res_1755007900942_338 = 1'b0;
            default: inj_out_res_1755007900942_338 = 1'b1;
        endcase
    end
    // END: casez_xz_ts1755007900942

    assign inj_out_c_1755007900941_356 = {inj_in_h_1755007900941_571, inj_in_l_1755007900941_630};
    // END: concat_op_ts1755007900942
endmodule

