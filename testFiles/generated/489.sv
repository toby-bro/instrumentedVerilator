module mod_statement_block_var (
    input logic in_c,
    output logic out_c
);
    always_comb begin : block_with_vars
        int   block_local_int;
        logic [7:0] block_local_logic;
        block_local_int   = in_c ? 10 : 20;
        block_local_logic = block_local_int;
        out_c             = block_local_logic[0];
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_in_a_1755007917808_597,
    input logic [31:0] inj_nested_in_1755007917807_73,
    input wire reset,
    output logic [7:0] inj_inner_field_o_1755007917807_83,
    output logic inj_out_b_1755007917808_213,
    output logic inj_out_c_1755007917808_839
);
    // BEGIN: nested_types_mod_ts1755007917808
    typedef struct packed {
        logic [7:0] inner_field_ts1755007917808;
        logic [7:0] padding_ts1755007917808;
    } inner_struct_t;
    typedef union packed {
        logic [31:0] full_word_ts1755007917808;
        struct packed {
            logic [15:0] unused_ts1755007917808;
            inner_struct_t inner_data;
        } outer_fields;
    } outer_union_t;
    outer_union_t nested_var;
    // BEGIN: LintUnusedSignal_ts1755007917808
    logic unused_w_ts1755007917808; 
    mod_statement_block_var mod_statement_block_var_inst_1755007917808_8805 (
        .out_c(inj_out_c_1755007917808_839),
        .in_c(inj_in_a_1755007917808_597)
    );
    assign inj_out_b_1755007917808_213 = inj_in_a_1755007917808_597;
    // END: LintUnusedSignal_ts1755007917808

    always_comb begin
        nested_var.full_word_ts1755007917808 = inj_nested_in_1755007917807_73;
    end
    assign inj_inner_field_o_1755007917807_83 = nested_var.outer_fields.inner_data.inner_field_ts1755007917808;
    // END: nested_types_mod_ts1755007917808
endmodule

