module formatting_stress (
    input logic [1:0] case_sel_fmt,
    input logic [7:0] data_in_fmt,
    input logic enable_block_fmt,
    input logic sel_fmt,
    output logic [7:0] data_out_fmt
);
    logic [7:0] temp_reg_fmt; 
    always_comb begin : stress_comb_block_label 
        data_out_fmt = 8'hXX; 
        if (enable_block_fmt) begin
            if (sel_fmt) begin
                case (case_sel_fmt) 
                    2'b00: data_out_fmt = data_in_fmt;
                    2'b01: begin 
                        data_out_fmt = ~data_in_fmt; 
                        end 
                    2'b10: begin 
                        logic [7:0] added_val; 
                        added_val = data_in_fmt + 8'h01; 
                        data_out_fmt = added_val; 
                        end 
                    default: data_out_fmt = 8'hFF; 
                endcase 
            end else begin
                data_out_fmt = data_in_fmt - 8'h01; 
            end 
        end else begin
            data_out_fmt = 8'h00; 
        end 
    end
endmodule

module module_with_param (
    input logic in,
    output logic named_out
);
    parameter int DELAY = 10;
    logic bind_dummy_in;
    logic bind_dummy_out;
    assign named_out = in;
endmodule

module snippet (
    input wire clk,
    input logic [1:0] inj_case_sel_fmt_1755007892703_37,
    input logic [9:0] inj_data_in_pl_1755007892696_390,
    input logic inj_in_1755007892693_650,
    input logic [7:0] inj_in_1755007892695_240,
    input logic [2:0] inj_in_val_1755007892693_894,
    input int inj_in_val_1755007892694_186,
    input wire reset,
    output wire inj_data_d_1755007892698_613,
    output logic [7:0] inj_data_out_fmt_1755007892703_266,
    output logic [4:0] inj_data_out_pl_1755007892696_233,
    output logic inj_fs_out_target_1755007892697_749,
    output logic [15:0] inj_lc_val_1755007892693_508,
    output logic inj_named_out_1755007892693_477,
    output logic inj_out_1755007892695_747,
    output logic [7:0] inj_out_mv_a_1755007892700_183,
    output logic [7:0] inj_out_mv_b_1755007892700_779,
    output logic [7:0] inj_out_mv_c_1755007892700_197,
    output reg inj_out_res_1755007892693_648,
    output int inj_out_val_1755007892694_285,
    output int inj_out_val_1755007892699_979,
    output logic inj_reset_1755007892695_423
);
    // BEGIN: macro_line_continuation_user_ts1755007892693
    `define MULTI_VAL                \
        16'hABCD
    `define ADD_FIVE(v)              \
        ((v) +                         \
            5)
    logic [15:0] value_reg_ts1755007892693;
        // BEGIN: cu_timeunit_mod_ts1755007892695
        logic internal_sig_ts1755007892695;
            // BEGIN: module_packed_logic_ts1755007892696
            logic [15:0] my_packed_logic_ts1755007892696 ;
                // BEGIN: mod_split_multiple_vars_ts1755007892701
                logic [7:0]  split_mv_var_ts1755007892701;
                logic [7:0] other_mv_var1_ts1755007892701;
                logic [7:0] other_mv_var2_ts1755007892701;
                    formatting_stress formatting_stress_inst_1755007892703_1448 (
                        .case_sel_fmt(inj_case_sel_fmt_1755007892703_37),
                        .data_in_fmt(other_mv_var2_ts1755007892701),
                        .enable_block_fmt(internal_sig_ts1755007892695),
                        .sel_fmt(inj_in_1755007892693_650),
                        .data_out_fmt(inj_data_out_fmt_1755007892703_266)
                    );
                always_ff @(posedge clk or posedge reset) begin
                    if (reset) begin
                        split_mv_var_ts1755007892701 <= 8'b0;
                        other_mv_var1_ts1755007892701 <= 8'b0;
                        other_mv_var2_ts1755007892701 <= 8'b0;
                    end else begin
                        split_mv_var_ts1755007892701 <= inj_in_1755007892695_240;
                        other_mv_var1_ts1755007892701 <= inj_in_1755007892695_240 + 1;
                        other_mv_var2_ts1755007892701 <= inj_in_1755007892695_240 + 2;
                        if (inj_in_1755007892695_240 > 100) begin
                            split_mv_var_ts1755007892701 <= 8'hFF;
                        end
                        inj_out_mv_a_1755007892700_183 <= split_mv_var_ts1755007892701;
                        inj_out_mv_b_1755007892700_779 <= other_mv_var1_ts1755007892701;
                        inj_out_mv_c_1755007892700_197 <= other_mv_var2_ts1755007892701;
                    end
                end
                // END: mod_split_multiple_vars_ts1755007892701

                // BEGIN: invalid_this_diag_mod_ts1755007892699
                assign inj_out_val_1755007892699_979 = inj_in_val_1755007892694_186;
                // END: invalid_this_diag_mod_ts1755007892699

                // BEGIN: simple_logic_b_ts1755007892698
                assign inj_data_d_1755007892698_613 = clk;
                // END: simple_logic_b_ts1755007892698

                // BEGIN: mod_fixup_target_ts1755007892697
                assign inj_fs_out_target_1755007892697_749 = inj_in_1755007892693_650;
                // END: mod_fixup_target_ts1755007892697

            always_comb begin
                my_packed_logic_ts1755007892696[9:0] = inj_data_in_pl_1755007892696_390;
                my_packed_logic_ts1755007892696[15:10] = 6'h3F;
                my_packed_logic_ts1755007892696[0] = inj_in_1755007892693_650;
            end
            assign inj_data_out_pl_1755007892696_233[4:1] = my_packed_logic_ts1755007892696[4:1];
            assign inj_data_out_pl_1755007892696_233[0] = my_packed_logic_ts1755007892696[1];
            // END: module_packed_logic_ts1755007892696

        always_ff @(posedge clk) begin
            inj_reset_1755007892695_423 <= 1'b0;
            internal_sig_ts1755007892695 = clk;
        end
        // END: cu_timeunit_mod_ts1755007892695

        // BEGIN: variable_sel_mux_ts1755007892695
        assign inj_out_1755007892695_747 = inj_in_1755007892695_240[inj_in_val_1755007892693_894];
        // END: variable_sel_mux_ts1755007892695

        // BEGIN: definition_used_diag_mod_ts1755007892694
        assign inj_out_val_1755007892694_285 = inj_in_val_1755007892694_186;
        // END: definition_used_diag_mod_ts1755007892694

        // BEGIN: casez_xz_ts1755007892694
        always_comb begin
            inj_out_res_1755007892693_648 = 1'b0;
            casez (inj_in_val_1755007892693_894)
                3'b1??: inj_out_res_1755007892693_648 = 1'b1;
                3'b0z?: inj_out_res_1755007892693_648 = 1'b0;
                default: inj_out_res_1755007892693_648 = 1'b1;
            endcase
        end
        // END: casez_xz_ts1755007892694

    always_comb begin
        if (inj_in_1755007892693_650)
            value_reg_ts1755007892693 = `MULTI_VAL;
        else
            value_reg_ts1755007892693 = `ADD_FIVE(16'h0010);
    end
    assign inj_lc_val_1755007892693_508 = value_reg_ts1755007892693;
    // END: macro_line_continuation_user_ts1755007892693

    module_with_param module_with_param_inst_1755007892693_2122 (
        .in(inj_in_1755007892693_650),
        .named_out(inj_named_out_1755007892693_477)
    );
endmodule

