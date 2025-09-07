module ModRegister (
    input logic din,
    output logic dout
);
    always @* begin
        dout = din;
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_data_in_1755007808086_205,
    input logic inj_in_a_1755007808089_619,
    input logic inj_tok_in_1755007808086_296,
    input wire reset,
    output logic inj_dout_1755007808090_459,
    output logic [7:0] inj_out_1755007808088_584,
    output logic inj_out_comb_1755007808089_124,
    output logic [7:0] inj_out_mv_a_1755007808086_818,
    output logic [7:0] inj_out_mv_b_1755007808086_9,
    output logic [7:0] inj_out_mv_c_1755007808086_296,
    output logic inj_out_reg_1755007808089_661,
    output logic [7:0] inj_out_val_1755007808088_773,
    output logic [7:0] inj_out_var_1755007808092_790,
    output logic [7:0] inj_out_vec_1755007808091_462,
    output logic inj_tok_out_1755007808086_407
);
    // BEGIN: Module_MacroTokens_ts1755007808086
    // BEGIN: mod_split_multiple_vars_ts1755007808087
    logic [7:0]  split_mv_var_ts1755007808087;
    logic [7:0] other_mv_var1_ts1755007808087;
    logic [7:0] other_mv_var2_ts1755007808087;
        // BEGIN: ModClockedWithSimpleAssign_ts1755007808089
        logic internal_reg_ts1755007808089;
            // BEGIN: not_a_hierarchical_scope_diag_mod_ts1755007808092
            logic [7:0] simple_var_nahsdm_ts1755007808092;
            always_comb simple_var_nahsdm_ts1755007808092 = split_mv_var_ts1755007808087;
            assign inj_out_var_1755007808092_790 = simple_var_nahsdm_ts1755007808092;
            // END: not_a_hierarchical_scope_diag_mod_ts1755007808092

            // BEGIN: SimpleLoopExample_ts1755007808091
            always_comb begin
                for (int i = 0; i < 8; i++) begin
                    inj_out_vec_1755007808091_462[i] = split_mv_var_ts1755007808087[7 - i];
                end
            end
            // END: SimpleLoopExample_ts1755007808091

            ModRegister ModRegister_inst_1755007808090_8437 (
                .dout(inj_dout_1755007808090_459),
                .din(inj_tok_in_1755007808086_296)
            );
        always @(posedge clk) begin 
        internal_reg_ts1755007808089 <= inj_in_a_1755007808089_619; 
        end
        assign inj_out_comb_1755007808089_124 = inj_in_a_1755007808089_619 ^ inj_tok_in_1755007808086_296; 
        always @(posedge clk) begin 
        inj_out_reg_1755007808089_661 <= internal_reg_ts1755007808089 & inj_tok_in_1755007808086_296; 
        end
        // END: ModClockedWithSimpleAssign_ts1755007808089

        // BEGIN: deep_logic_ts1755007808088
        assign inj_out_1755007808088_584 = (((other_mv_var1_ts1755007808087 & inj_data_in_1755007808086_205) | (~split_mv_var_ts1755007808087)) ^ (other_mv_var1_ts1755007808087 + inj_data_in_1755007808086_205)) - (split_mv_var_ts1755007808087 << 2);
        // END: deep_logic_ts1755007808088

        // BEGIN: generic_class_scope_diag_mod_ts1755007808088
        assign inj_out_val_1755007808088_773 = split_mv_var_ts1755007808087;
        // END: generic_class_scope_diag_mod_ts1755007808088

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_mv_var_ts1755007808087 <= 8'b0;
            other_mv_var1_ts1755007808087 <= 8'b0;
            other_mv_var2_ts1755007808087 <= 8'b0;
        end else begin
            split_mv_var_ts1755007808087 <= inj_data_in_1755007808086_205;
            other_mv_var1_ts1755007808087 <= inj_data_in_1755007808086_205 + 1;
            other_mv_var2_ts1755007808087 <= inj_data_in_1755007808086_205 + 2;
            if (inj_data_in_1755007808086_205 > 100) begin
                split_mv_var_ts1755007808087 <= 8'hFF;
            end
            inj_out_mv_a_1755007808086_818 <= split_mv_var_ts1755007808087;
            inj_out_mv_b_1755007808086_9 <= other_mv_var1_ts1755007808087;
            inj_out_mv_c_1755007808086_296 <= other_mv_var2_ts1755007808087;
        end
    end
    // END: mod_split_multiple_vars_ts1755007808087

    `define PASTE(a,b) a``b
    logic `PASTE(my,_var);
    always_comb begin
        `PASTE(my,_var) = inj_tok_in_1755007808086_296;
        inj_tok_out_1755007808086_407         = `PASTE(my,_var);
    end
    // END: Module_MacroTokens_ts1755007808086
endmodule

