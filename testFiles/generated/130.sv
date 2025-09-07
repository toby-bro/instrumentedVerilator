interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module basic_d_flipflop (
    input logic clk,
    input logic d,
    output logic q
);
    always_ff @(posedge clk) begin
        q <= d;
    end
endmodule

module case_default (
    input logic [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b01: out_res = 1'b1;
            2'b10: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule

module cast_select_demo (
    input logic [7:0] in_data,
    output logic [1:0] out_bits
);
    logic [7:0] internal;
    always_comb begin
        internal = in_data;
        out_bits = internal[3 -: 2];
    end
endmodule

module definition_used_diag_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module div_mod_ops (
    input logic [7:0] denominator,
    input logic [15:0] dividend_mod,
    input logic [7:0] divisor_mod,
    input logic [15:0] numerator,
    output logic [15:0] quotient,
    output logic [7:0] remainder
);
    assign quotient = (denominator == 0) ? 16'hFFFF : (numerator / denominator); 
    assign remainder = (divisor_mod == 0) ? 8'hFF : (dividend_mod % divisor_mod);
endmodule

module mod_fixup_target (
    input logic fs_in_target,
    output logic fs_out_target
);
    assign fs_out_target = fs_in_target;
endmodule

module snippet #(
    parameter int P_PORT_VAL = 25
) (
    input wire clk,
    input bit inj_condition_m10_1755007796551_205,
    input logic [9:0] inj_data_in_pl_1755007796558_528,
    input logic [15:0] inj_dividend_mod_1755007796557_935,
    input logic inj_fs_in_target_1755007796550_581,
    input int inj_in_val_1755007796552_564,
    input logic [1:0] inj_in_val_1755007796563_248,
    input logic [7:0] inj_in_val_m10_1755007796551_829,
    input logic [15:0] inj_in_vec_1755007796555_523,
    input logic [31:0] inj_nested_in_1755007796565_41,
    input logic inj_sel_fmt_1755007796567_40,
    input logic [2:0] inj_selector_1755007796550_295,
    input logic [3:0] inj_v1_1755007796551_308,
    input logic [3:0] inj_v2_1755007796551_146,
    input wire reset,
    output wire inj_data_d_1755007796556_337,
    output logic [7:0] inj_data_out_fmt_1755007796567_435,
    output logic [4:0] inj_data_out_pl_1755007796558_518,
    output logic inj_eq_1755007796551_504,
    output logic inj_fs_out_target_1755007796550_248,
    output logic [7:0] inj_inner_field_o_1755007796565_873,
    output logic [7:0] inj_o_sum_1755007796554_879,
    output logic [1:0] inj_out_bits_1755007796553_324,
    output logic inj_out_g_1755007796559_931,
    output logic inj_out_pd_1755007796552_870,
    output reg inj_out_res_1755007796563_343,
    output logic [7:0] inj_out_slice_be_1755007796555_900,
    output logic [7:0] inj_out_slice_le_1755007796555_907,
    output int inj_out_val_1755007796552_795,
    output logic [7:0] inj_out_val_m10_1755007796551_162,
    output logic inj_out_valid_status_1755007796561_233,
    output logic inj_q_1755007796550_186,
    output logic [15:0] inj_quotient_1755007796557_867,
    output logic [7:0] inj_remainder_1755007796557_444,
    output logic [3:0] inj_result_out_1755007796550_968,
    output logic inj_y_1755007796571_38
);
    // BEGIN: rand_case_mod_ts1755007796550
    // BEGIN: unsupported_cond_expr_ts1755007796551
    logic [7:0] var_m10_ts1755007796551;
        // BEGIN: module_packed_logic_ts1755007796558
        logic [15:0] my_packed_logic_ts1755007796558 ;
            // BEGIN: formatting_stress_ts1755007796568
            logic [7:0] temp_reg_fmt_ts1755007796568; 
            always_comb begin : stress_comb_block_label 
                inj_data_out_fmt_1755007796567_435 = 8'hXX; 
                if (inj_fs_in_target_1755007796550_581) begin
                    if (inj_sel_fmt_1755007796567_40) begin
                        case (inj_in_val_1755007796563_248) 
                            2'b00: inj_data_out_fmt_1755007796567_435 = var_m10_ts1755007796551;
                            2'b01: begin 
                                inj_data_out_fmt_1755007796567_435 = ~var_m10_ts1755007796551; 
                                end 
                            2'b10: begin 
                                logic [7:0] added_val_ts1755007796568; 
                                    // BEGIN: ModSimpleLogic_ts1755007796571
                                    assign inj_y_1755007796571_38 = inj_sel_fmt_1755007796567_40 ^ inj_fs_in_target_1755007796550_581;
                                    // END: ModSimpleLogic_ts1755007796571

                                added_val_ts1755007796568 = var_m10_ts1755007796551 + 8'h01; 
                                inj_data_out_fmt_1755007796567_435 = added_val_ts1755007796568; 
                                end 
                            default: inj_data_out_fmt_1755007796567_435 = 8'hFF; 
                        endcase 
                    end else begin
                        inj_data_out_fmt_1755007796567_435 = var_m10_ts1755007796551 - 8'h01; 
                    end 
                end else begin
                    inj_data_out_fmt_1755007796567_435 = 8'h00; 
                end 
            end
            // END: formatting_stress_ts1755007796568

            // BEGIN: nested_types_mod_ts1755007796565
            typedef struct packed {
                logic [7:0] inner_field_ts1755007796565;
                logic [7:0] padding_ts1755007796565;
            } inner_struct_t;
            typedef union packed {
                logic [31:0] full_word_ts1755007796565;
                struct packed {
                    logic [15:0] unused_ts1755007796565;
                    inner_struct_t inner_data;
                } outer_fields;
            } outer_union_t;
            outer_union_t nested_var;
            always_comb begin
                nested_var.full_word_ts1755007796565 = inj_nested_in_1755007796565_41;
            end
            assign inj_inner_field_o_1755007796565_873 = nested_var.outer_fields.inner_data.inner_field_ts1755007796565;
            // END: nested_types_mod_ts1755007796565

            case_default case_default_inst_1755007796563_2246 (
                .in_val(inj_in_val_1755007796563_248),
                .out_res(inj_out_res_1755007796563_343)
            );
            // BEGIN: module_assign_blocking_ts1755007796561
            my_if vif_inst();
            always_comb begin
                vif_inst.data = var_m10_ts1755007796551;
                vif_inst.valid = 1'b1;
                vif_inst.ready = 1'b0;
                inj_out_valid_status_1755007796561_233 = vif_inst.valid;
            end
            // END: module_assign_blocking_ts1755007796561

            // BEGIN: LintSeqNonBlockAssign_ts1755007796559
            always_ff @(posedge clk) begin
                inj_out_g_1755007796559_931 <= inj_fs_in_target_1755007796550_581;
            end
            // END: LintSeqNonBlockAssign_ts1755007796559

        always_comb begin
            my_packed_logic_ts1755007796558[9:0] = inj_data_in_pl_1755007796558_528;
            my_packed_logic_ts1755007796558[15:10] = 6'h3F;
            my_packed_logic_ts1755007796558[0] = inj_fs_in_target_1755007796550_581;
        end
        assign inj_data_out_pl_1755007796558_518[4:1] = my_packed_logic_ts1755007796558[4:1];
        assign inj_data_out_pl_1755007796558_518[0] = my_packed_logic_ts1755007796558[1];
        // END: module_packed_logic_ts1755007796558

        div_mod_ops div_mod_ops_inst_1755007796557_9919 (
            .denominator(var_m10_ts1755007796551),
            .dividend_mod(inj_dividend_mod_1755007796557_935),
            .divisor_mod(inj_in_val_m10_1755007796551_829),
            .numerator(inj_in_vec_1755007796555_523),
            .quotient(inj_quotient_1755007796557_867),
            .remainder(inj_remainder_1755007796557_444)
        );
        // BEGIN: simple_logic_b_ts1755007796556
        assign inj_data_d_1755007796556_337 = reset;
        // END: simple_logic_b_ts1755007796556

        // BEGIN: range_select_simple_packed_ts1755007796555
        assign inj_out_slice_be_1755007796555_900 = inj_in_vec_1755007796555_523[7:0]; 
        assign inj_out_slice_le_1755007796555_907 = inj_in_vec_1755007796555_523[7:0]; 
        // END: range_select_simple_packed_ts1755007796555

        // BEGIN: param_local_port_ts1755007796554
        localparam int LP_BODY_VAL = 125;
        localparam int LP_CALCULATED = P_PORT_VAL + LP_BODY_VAL;
        always_comb begin
            if (reset) begin
                inj_o_sum_1755007796554_879 = 0;
            end else begin
                inj_o_sum_1755007796554_879 = LP_CALCULATED;
            end
        end
        // END: param_local_port_ts1755007796554

        cast_select_demo cast_select_demo_inst_1755007796553_1373 (
            .out_bits(inj_out_bits_1755007796553_324),
            .in_data(var_m10_ts1755007796551)
        );
        // BEGIN: ProgramDefinition_ts1755007796552
        assign inj_out_pd_1755007796552_870 = clk;
        // END: ProgramDefinition_ts1755007796552

        definition_used_diag_mod definition_used_diag_mod_inst_1755007796552_2717 (
            .in_val(inj_in_val_1755007796552_564),
            .out_val(inj_out_val_1755007796552_795)
        );
        // BEGIN: ModCompareVec_ts1755007796551
        assign inj_eq_1755007796551_504 = (inj_v1_1755007796551_308 == inj_v2_1755007796551_146);
        // END: ModCompareVec_ts1755007796551

    always_comb begin
        var_m10_ts1755007796551 = inj_in_val_m10_1755007796551_829;
        inj_out_val_m10_1755007796551_162 = inj_condition_m10_1755007796551_205 ? var_m10_ts1755007796551 : var_m10_ts1755007796551;
        var_m10_ts1755007796551++;
    end
    // END: unsupported_cond_expr_ts1755007796551

    basic_d_flipflop basic_d_flipflop_inst_1755007796550_1846 (
        .q(inj_q_1755007796550_186),
        .clk(clk),
        .d(inj_fs_in_target_1755007796550_581)
    );
    always_comb begin
        case (inj_selector_1755007796550_295)
            0: inj_result_out_1755007796550_968 = 4'h0;
            1: inj_result_out_1755007796550_968 = 4'h1;
            2: inj_result_out_1755007796550_968 = 4'hA;
            default: inj_result_out_1755007796550_968 = 4'hF;
        endcase
    end
    // END: rand_case_mod_ts1755007796550

    mod_fixup_target mod_fixup_target_inst_1755007796550_9091 (
        .fs_in_target(inj_fs_in_target_1755007796550_581),
        .fs_out_target(inj_fs_out_target_1755007796550_248)
    );
endmodule

