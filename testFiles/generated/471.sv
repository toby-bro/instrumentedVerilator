typedef struct packed {
    logic [3:0] f1;
    logic       f2;
    logic [2:0] f3;
} eight_bit_unpacked_struct_t;
typedef struct packed {
    logic [3:0] f1;
    logic f2;
    logic [2:0] f3;
} eight_bit_unpacked_struct_t;

module Comb_Loop (
    input wire loop_in,
    output wire loop_out
);
    wire loop_wire1;
    wire loop_wire2;
    assign loop_wire1 = loop_wire2 | loop_in;
    assign loop_wire2 = loop_wire1; 
    assign loop_out = loop_wire1;
endmodule

module Mod_BasicOps (
    input wire [7:0] in_a,
    input wire [7:0] in_b,
    input wire in_bit,
    input wire [7:0] in_c,
    input wire [7:0] in_const1,
    input wire [7:0] in_const2,
    output logic [7:0] out_add_assoc,
    output logic [7:0] out_and_assoc,
    output logic [7:0] out_and_swap_const,
    output logic [7:0] out_arith,
    output logic [7:0] out_bitwise,
    output logic out_logical,
    output logic [7:0] out_mul_assoc,
    output logic [7:0] out_negate,
    output logic [7:0] out_or_assoc,
    output logic [7:0] out_or_swap_not,
    output logic [7:0] out_unary_not,
    output logic [7:0] out_xor_assoc,
    output logic [7:0] out_xor_swap_var
);
    logic [7:0] intermediate_arith;
    logic [7:0] intermediate_bitwise;
    logic [0:0] intermediate_logical;
    logic [7:0] intermediate_add_assoc;
    logic [7:0] intermediate_mul_assoc;
    logic [7:0] intermediate_and_assoc;
    logic [7:0] intermediate_or_assoc;
    logic [7:0] intermediate_xor_assoc;
    parameter [7:0] CONST_ZERO = 8'h00;
    always_comb begin
        intermediate_arith = in_a;
        intermediate_arith = intermediate_arith + in_b;
        intermediate_arith = intermediate_arith - in_c;
        intermediate_arith = intermediate_arith * in_const1;
        if (in_b != CONST_ZERO) begin
            intermediate_arith = intermediate_arith / in_b;
            intermediate_arith = intermediate_arith % in_b;
        end else begin
            intermediate_arith = 'x;
        end
        out_arith = intermediate_arith;
        intermediate_bitwise = in_a;
        intermediate_bitwise = intermediate_bitwise & in_b;
        intermediate_bitwise = intermediate_bitwise | in_c;
        intermediate_bitwise = intermediate_bitwise ^ in_const1;
        out_bitwise = intermediate_bitwise;
        intermediate_logical = (in_a != CONST_ZERO) && (in_b != CONST_ZERO);
        intermediate_logical = intermediate_logical || (in_c != CONST_ZERO);
        out_logical = !intermediate_logical;
        out_unary_not = ~in_a;
        out_negate = -in_a;
        intermediate_add_assoc = (in_a + in_b) + in_c;
        out_add_assoc = intermediate_add_assoc;
        intermediate_mul_assoc = (in_a * in_b) * in_c;
        out_mul_assoc = intermediate_mul_assoc;
        intermediate_and_assoc = (in_a & in_b) & in_c;
        out_and_assoc = intermediate_and_assoc;
        intermediate_or_assoc = (in_a | in_b) | in_c;
        out_or_assoc = intermediate_or_assoc;
        intermediate_xor_assoc = (in_a ^ in_b) ^ in_c;
        out_xor_assoc = intermediate_xor_assoc;
        out_and_swap_const = in_const1 & in_a;
        out_or_swap_not = (~in_a) | in_b;
        out_xor_swap_var = in_b ^ in_c;
    end
endmodule

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

module bitwise_ops (
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [7:0] in3,
    output logic [7:0] out
);
    assign out = (in1 & in2) | (~in3) ^ (in1 << 2) >> 1;
endmodule

module deep_ff_control_logic (
    input wire dffcl_clk,
    input wire [3:0] dffcl_ctrl_mode,
    input wire [15:0] dffcl_data_in1,
    input wire [15:0] dffcl_data_in2,
    input wire dffcl_rst_n,
    output logic [15:0] dffcl_data_out
);
    always_ff @(posedge dffcl_clk or negedge dffcl_rst_n) begin
    if (!dffcl_rst_n) begin
        dffcl_data_out <= 16'h0000;
    end else begin
        case (dffcl_ctrl_mode)
            4'd0: dffcl_data_out <= dffcl_data_in1 + dffcl_data_in2;
            4'd1: begin
                if (dffcl_data_in1 > dffcl_data_in2) begin
                    case (dffcl_ctrl_mode[1:0])
                        2'b00: dffcl_data_out <= dffcl_data_in1 - dffcl_data_in2;
                        2'b01: dffcl_data_out <= dffcl_data_in1 & dffcl_data_in2;
                        default: dffcl_data_out <= dffcl_data_in1 | dffcl_data_in2;
                    endcase
                end else begin
                    case (dffcl_ctrl_mode[1:0])
                        2'b00: dffcl_data_out <= dffcl_data_in2 - dffcl_data_in1;
                        2'b01: dffcl_data_out <= dffcl_data_in1 ^ dffcl_data_in2;
                        default: dffcl_data_out <= ~dffcl_data_in1;
                    endcase
                end
            end
            4'd2: begin
                casez (dffcl_data_in1[15:13])
                    3'b000: dffcl_data_out <= dffcl_data_in2;
                    3'b001: dffcl_data_out <= ~dffcl_data_in2;
                    3'b01?: begin
                        if (dffcl_data_in2[0]) dffcl_data_out <= dffcl_data_in1 << 1;
                        else dffcl_data_out <= dffcl_data_in1 >> 1;
                    end
                    3'b1??: begin
                        if (dffcl_ctrl_mode[0]) dffcl_data_out <= dffcl_data_in1 + 1;
                        else dffcl_data_out <= dffcl_data_in1 - 1;
                    end
                    default: dffcl_data_out <= 16'hAAAA;
                endcase
            end
            default: begin
                if (dffcl_ctrl_mode[2]) dffcl_data_out <= dffcl_data_in1;
                else dffcl_data_out <= dffcl_data_in2;
            end
        endcase
    end
    end
endmodule

module explicit_non_ansi_ports_module (
    dummy_in_non_ansi,
    named_conn_in,
    dummy_out_non_ansi,
    named_conn_out
);
    input logic named_conn_in;
    output logic named_conn_out;
    input logic dummy_in_non_ansi;
    output logic dummy_out_non_ansi;
    assign named_conn_out = named_conn_in;
    assign dummy_out_non_ansi = dummy_in_non_ansi;
endmodule

module mod_split_if (
    input logic clk,
    input logic cond,
    input logic [7:0] data_in,
    input logic reset,
    output logic [7:0] out_if_a,
    output logic [7:0] out_if_b
);
    logic [7:0]  split_if_var;
    logic [7:0] other_if_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_if_var <= 8'b0;
            other_if_var <= 8'b0;
        end else begin
            if (cond) begin
                split_if_var <= data_in;
                other_if_var <= data_in + 3;
            end else begin
                split_if_var <= data_in - 1;
                other_if_var <= data_in - 2;
            end
        end
    end
    always_comb begin
        out_if_a = split_if_var;
        out_if_b = other_if_var;
    end
endmodule

module mod_sub (
    input wire in_sub,
    output logic out_sub
);
    assign out_sub = in_sub;
endmodule

module recursive_param_diag_mod (
    input int dummy_in,
    output int out_val
);
    assign out_val = dummy_in;
endmodule

module typedef_union_mod (
    input logic [15:0] packed_in,
    output logic [7:0] field0_byte_o
);
    typedef union packed {
        logic [15:0] word;
        logic [1:0][7:0] byte_fields;
    } my_packed_union_t;
    my_packed_union_t my_union_var;
    always_comb begin
        my_union_var.word = packed_in;
    end
    assign field0_byte_o = my_union_var.byte_fields[0];
endmodule

module snippet #(
    parameter int WIDTH = 8
) (
    input wire clk,
    input logic [7:0] inj_c_1755007911612_114,
    input logic [1:0] inj_case_expr_1755007911600_906,
    input logic [3:0] inj_concat_in_1755007911617_545,
    input wire [3:0] inj_dffcl_ctrl_mode_1755007911602_930,
    input wire [15:0] inj_dffcl_data_in1_1755007911602_91,
    input wire [15:0] inj_dffcl_data_in2_1755007911602_999,
    input logic inj_fs_in_target_1755007911600_105,
    input logic inj_i_data_sync_1755007911600_884,
    input logic [7:0] inj_in_1755007911599_556,
    input wire [7:0] inj_in_a_1755007911604_968,
    input wire [7:0] inj_in_b_1755007911604_539,
    input wire [7:0] inj_in_c_1755007911604_486,
    input bit [7:0] inj_in_cmd_1755007911618_241,
    input wire [7:0] inj_in_const1_1755007911604_835,
    input wire [7:0] inj_in_const2_1755007911604_106,
    input logic [38:0] inj_in_packed_for_conv_1755007911607_56,
    input logic [2:0] inj_in_val_1755007911599_241,
    input logic [15:0] inj_packed_in_1755007911605_196,
    input logic [3:0] inj_val_b_1755007911646_483,
    input logic [63:0] inj_wide_a_1755007911663_523,
    input logic [63:0] inj_wide_b_1755007911663_360,
    input logic [63:0] inj_wide_c_1755007911663_173,
    input wire reset,
    output logic [7:0] inj_concat_out_1755007911617_18,
    output reg [7:0] inj_data_out_1755007911609_44,
    output logic [7:0] inj_data_out_1755007911614_942,
    output logic [15:0] inj_dffcl_data_out_1755007911602_582,
    output bit inj_diag_output_flag_1755007911628_409,
    output logic [7:0] inj_dout_1755007911613_253,
    output logic inj_dummy_1755007911641_965,
    output logic inj_dummy_out_non_ansi_1755007911601_395,
    output logic [7:0] inj_field0_byte_o_1755007911605_348,
    output logic [7:0] inj_field0_byte_o_1755007911637_364,
    output logic inj_fs_out_target_1755007911600_542,
    output logic [4:0] inj_internal_out_1755007911600_222,
    output wire inj_loop_out_1755007911603_960,
    output logic inj_named_conn_out_1755007911601_328,
    output logic inj_o_1755007911622_276,
    output logic inj_o_reg_out_1755007911600_382,
    output logic inj_o_sum_1755007911651_293,
    output wire inj_o_wire_out_1755007911600_660,
    output logic [7:0] inj_out_1755007911599_632,
    output logic [7:0] inj_out_1755007911615_128,
    output wire inj_out_1755007911632_77,
    output logic [7:0] inj_out_add_assoc_1755007911604_115,
    output logic [7:0] inj_out_and_assoc_1755007911604_776,
    output logic [7:0] inj_out_and_swap_const_1755007911604_669,
    output logic [7:0] inj_out_arith_1755007911604_863,
    output logic inj_out_bit_conv_1755007911607_920,
    output logic [7:0] inj_out_bitwise_1755007911604_428,
    output logic [3:0] inj_out_h_1755007911621_303,
    output logic [7:0] inj_out_if_a_1755007911620_862,
    output logic [7:0] inj_out_if_b_1755007911620_909,
    output int inj_out_int_conv_1755007911607_178,
    output logic [3:0] inj_out_l_1755007911621_247,
    output logic inj_out_logical_1755007911604_405,
    output logic [7:0] inj_out_mul_assoc_1755007911604_345,
    output logic [7:0] inj_out_negate_1755007911604_327,
    output logic [7:0] inj_out_or_assoc_1755007911604_577,
    output logic [7:0] inj_out_or_swap_not_1755007911604_603,
    output reg inj_out_res_1755007911599_100,
    output bit [3:0] inj_out_status_1755007911618_645,
    output logic inj_out_sub_1755007911624_191,
    output logic [7:0] inj_out_unary_not_1755007911604_358,
    output logic [7:0] inj_out_unpacked_struct_repacked_1755007911607_476,
    output int inj_out_val_1755007911613_86,
    output int inj_out_val_1755007911616_810,
    output logic [7:0] inj_out_val_o_1755007911668_266,
    output logic [5:0] inj_out_vec_conv_1755007911607_522,
    output logic [7:0] inj_out_xor_assoc_1755007911604_503,
    output logic [7:0] inj_out_xor_swap_var_1755007911604_330,
    output logic [3:0] inj_result_1755007911646_793,
    output logic [7:0] inj_result_and_1755007911612_836,
    output logic [7:0] inj_result_or_1755007911612_243,
    output logic [7:0] inj_result_xor_1755007911612_11,
    output logic inj_sub_out_1755007911657_439,
    output logic [63:0] inj_wide_out_1755007911663_486,
    output logic [7:0] inj_wide_reg_1755007911651_590
);
    // BEGIN: casez_xz_ts1755007911599
    // BEGIN: sequential_always_assign_ts1755007911599
    // BEGIN: case_unique0_violating_mod_ts1755007911600
    // BEGIN: mod_fixup_target_ts1755007911600
    // BEGIN: nets_alias_clocking_ts1755007911601
    wire  w_internal_ts1755007911601;
    logic r_internal_ts1755007911601;
        // BEGIN: assign_pattern_lvalue_ts1755007911608
        eight_bit_unpacked_struct_t unpacked_s;
        logic [7:0] reg_unpacked_struct_repacked_ts1755007911607;
        int int_var_ts1755007911607;
        logic bit_var_ts1755007911607;
        logic [5:0] vec_var_ts1755007911607;
            // BEGIN: Module_ControlFlow_ts1755007911610
            reg [7:0] temp_ts1755007911610;
                // BEGIN: macro_concat_user_ts1755007911617
                `define MAKE_NAME(a,b) a``b
                logic var_signal_ts1755007911617;
                    // BEGIN: mod_lint_target_ts1755007911651
                    logic l_reg_ts1755007911651;
                        // BEGIN: split_conditional_blocking_ts1755007911669
                        always @(*) begin
                            if (l_reg_ts1755007911651) begin
                                inj_out_val_o_1755007911668_266 = inj_c_1755007911612_114;
                            end else begin
                                inj_out_val_o_1755007911668_266 = reg_unpacked_struct_repacked_ts1755007911607;
                            end
                        end
                        // END: split_conditional_blocking_ts1755007911669

                        // BEGIN: wide_ops_deep_ts1755007911663
                        assign inj_wide_out_1755007911663_486 = (((inj_wide_a_1755007911663_523 + inj_wide_b_1755007911663_360) ^ inj_wide_c_1755007911663_173) & (~inj_wide_a_1755007911663_523 | inj_wide_b_1755007911663_360)) + (inj_wide_c_1755007911663_173 >>> 5);
                        // END: wide_ops_deep_ts1755007911663

                        // BEGIN: sub_module_ts1755007911657
                        assign inj_sub_out_1755007911657_439 = !inj_i_data_sync_1755007911600_884;
                        // END: sub_module_ts1755007911657

                    always_comb begin
                        l_reg_ts1755007911651 = 1;
                        inj_wide_reg_1755007911651_590 = {reset, clk};
                    end
                    assign inj_o_sum_1755007911651_293 = reset + clk;
                    // END: mod_lint_target_ts1755007911651

                    // BEGIN: CombinationalLogic_ts1755007911646
                    always_comb begin
                        if (inj_fs_in_target_1755007911600_105) begin
                            inj_result_1755007911646_793 = inj_concat_in_1755007911617_545 + inj_val_b_1755007911646_483;
                        end else begin
                            inj_result_1755007911646_793 = 4'h0;
                        end
                    end
                    // END: CombinationalLogic_ts1755007911646

                    // BEGIN: mod_err_event_constant_ts1755007911641
                    always @(posedge 1'b1) begin
                        inj_dummy_1755007911641_965 = ~inj_dummy_1755007911641_965;
                    end
                    // END: mod_err_event_constant_ts1755007911641

                    typedef_union_mod typedef_union_mod_inst_1755007911637_7937 (
                        .field0_byte_o(inj_field0_byte_o_1755007911637_364),
                        .packed_in(inj_packed_in_1755007911605_196)
                    );
                    // BEGIN: Comb_Assign_ts1755007911633
                    assign inj_out_1755007911632_77 = reset & w_internal_ts1755007911601;
                    // END: Comb_Assign_ts1755007911633

                    PragmaDiagnosticDirective PragmaDiagnosticDirective_inst_1755007911628_7590 (
                        .diag_output_flag(inj_diag_output_flag_1755007911628_409),
                        .diag_input_val(int_var_ts1755007911607)
                    );
                    mod_sub mod_sub_inst_1755007911624_5921 (
                        .out_sub(inj_out_sub_1755007911624_191),
                        .in_sub(clk)
                    );
                    // BEGIN: child_module_v2_config_dummy_ts1755007911623
                    assign inj_o_1755007911622_276 = bit_var_ts1755007911607 | bit_var_ts1755007911607; 
                    // END: child_module_v2_config_dummy_ts1755007911623

                    // BEGIN: concat_assign_ts1755007911621
                    assign {inj_out_h_1755007911621_303, inj_out_l_1755007911621_247} = inj_c_1755007911612_114;
                    // END: concat_assign_ts1755007911621

                    mod_split_if mod_split_if_inst_1755007911620_8301 (
                        .clk(clk),
                        .cond(r_internal_ts1755007911601),
                        .data_in(reg_unpacked_struct_repacked_ts1755007911607),
                        .reset(reset),
                        .out_if_a(inj_out_if_a_1755007911620_862),
                        .out_if_b(inj_out_if_b_1755007911620_909)
                    );
                    // BEGIN: mod_case_standard_ts1755007911618
                always_comb begin
                    case (inj_in_cmd_1755007911618_241)
                        8'd0, 8'd1, 8'd2: begin
                            inj_out_status_1755007911618_645 = 4'hA;
                        end
                        8'd3, 8'd4: begin
                            inj_out_status_1755007911618_645 = 4'hB;
                        end
                        default: begin
                            inj_out_status_1755007911618_645 = 4'hF;
                        end
                    endcase
                end
                    // END: mod_case_standard_ts1755007911618

                always_comb begin
                    `MAKE_NAME(var,_signal) = inj_concat_in_1755007911617_545[0];
                end
                assign inj_concat_out_1755007911617_18 = {4'b0, inj_concat_in_1755007911617_545[3:1], var_signal_ts1755007911617};
                // END: macro_concat_user_ts1755007911617

                // BEGIN: module_in_program_ref_ts1755007911616
                assign inj_out_val_1755007911616_810 = int_var_ts1755007911607;
                // END: module_in_program_ref_ts1755007911616

                bitwise_ops bitwise_ops_inst_1755007911615_6519 (
                    .in1(inj_in_1755007911599_556),
                    .in2(reg_unpacked_struct_repacked_ts1755007911607),
                    .in3(inj_c_1755007911612_114),
                    .out(inj_out_1755007911615_128)
                );
                // BEGIN: cu_base_ts1755007911614
                assign inj_data_out_1755007911614_942 = inj_in_1755007911599_556;
                // END: cu_base_ts1755007911614

                recursive_param_diag_mod recursive_param_diag_mod_inst_1755007911613_9234 (
                    .dummy_in(int_var_ts1755007911607),
                    .out_val(inj_out_val_1755007911613_86)
                );
                // BEGIN: Parameterized_ts1755007911613
                assign inj_dout_1755007911613_253 = reg_unpacked_struct_repacked_ts1755007911607;
                // END: Parameterized_ts1755007911613

                // BEGIN: BitwiseOperations_ts1755007911612
                assign inj_result_and_1755007911612_836 = reg_unpacked_struct_repacked_ts1755007911607 & inj_in_1755007911599_556;
                assign inj_result_or_1755007911612_243 = reg_unpacked_struct_repacked_ts1755007911607 | inj_c_1755007911612_114;
                assign inj_result_xor_1755007911612_11 = inj_in_1755007911599_556 ^ inj_c_1755007911612_114;
                // END: BitwiseOperations_ts1755007911612

            always_comb begin
                unique case (inj_in_val_1755007911599_241)
                    3'b000: temp_ts1755007911610 = inj_in_1755007911599_556;
                    3'b001: temp_ts1755007911610 = inj_in_1755007911599_556 + 1;
                    3'b010: temp_ts1755007911610 = inj_in_1755007911599_556 - 1;
                    default: temp_ts1755007911610 = 8'hAA;
                endcase
            end
            always_ff @(posedge clk or negedge reset) begin
                if (!reset)
                    inj_data_out_1755007911609_44 <= 8'h00;
                else
                    inj_data_out_1755007911609_44 <= temp_ts1755007911610;
            end
            // END: Module_ControlFlow_ts1755007911610

        always_comb begin
            unpacked_s.f1 = inj_in_1755007911599_556[3:0];
            unpacked_s.f2 = inj_in_1755007911599_556[4];
            unpacked_s.f3 = inj_in_1755007911599_556[7:5];
            reg_unpacked_struct_repacked_ts1755007911607 = { unpacked_s.f3, unpacked_s.f2, unpacked_s.f1 };
            int_var_ts1755007911607 = inj_in_packed_for_conv_1755007911607_56[31:0];
            bit_var_ts1755007911607 = inj_in_packed_for_conv_1755007911607_56[32];
            vec_var_ts1755007911607 = inj_in_packed_for_conv_1755007911607_56[38:33];
            inj_out_unpacked_struct_repacked_1755007911607_476 = reg_unpacked_struct_repacked_ts1755007911607;
            inj_out_int_conv_1755007911607_178 = int_var_ts1755007911607;
            inj_out_bit_conv_1755007911607_920 = bit_var_ts1755007911607;
            inj_out_vec_conv_1755007911607_522 = vec_var_ts1755007911607;
        end
        // END: assign_pattern_lvalue_ts1755007911608

        // BEGIN: typedef_union_mod_ts1755007911605
        typedef union packed {
            logic [15:0] word_ts1755007911605;
            logic [1:0][7:0] byte_fields_ts1755007911605;
        } my_packed_union_t;
        my_packed_union_t my_union_var;
        always_comb begin
            my_union_var.word_ts1755007911605 = inj_packed_in_1755007911605_196;
        end
        assign inj_field0_byte_o_1755007911605_348 = my_union_var.byte_fields_ts1755007911605[0];
        // END: typedef_union_mod_ts1755007911605

        Mod_BasicOps Mod_BasicOps_inst_1755007911604_995 (
            .in_bit(clk),
            .out_xor_swap_var(inj_out_xor_swap_var_1755007911604_330),
            .out_add_assoc(inj_out_add_assoc_1755007911604_115),
            .in_const2(inj_in_const2_1755007911604_106),
            .out_or_assoc(inj_out_or_assoc_1755007911604_577),
            .out_negate(inj_out_negate_1755007911604_327),
            .out_bitwise(inj_out_bitwise_1755007911604_428),
            .out_logical(inj_out_logical_1755007911604_405),
            .out_or_swap_not(inj_out_or_swap_not_1755007911604_603),
            .in_b(inj_in_b_1755007911604_539),
            .out_and_assoc(inj_out_and_assoc_1755007911604_776),
            .out_unary_not(inj_out_unary_not_1755007911604_358),
            .out_and_swap_const(inj_out_and_swap_const_1755007911604_669),
            .in_c(inj_in_c_1755007911604_486),
            .out_xor_assoc(inj_out_xor_assoc_1755007911604_503),
            .in_a(inj_in_a_1755007911604_968),
            .out_mul_assoc(inj_out_mul_assoc_1755007911604_345),
            .out_arith(inj_out_arith_1755007911604_863),
            .in_const1(inj_in_const1_1755007911604_835)
        );
        Comb_Loop Comb_Loop_inst_1755007911603_1967 (
            .loop_in(w_internal_ts1755007911601),
            .loop_out(inj_loop_out_1755007911603_960)
        );
        deep_ff_control_logic deep_ff_control_logic_inst_1755007911602_9665 (
            .dffcl_rst_n(reset),
            .dffcl_data_out(inj_dffcl_data_out_1755007911602_582),
            .dffcl_clk(clk),
            .dffcl_ctrl_mode(inj_dffcl_ctrl_mode_1755007911602_930),
            .dffcl_data_in1(inj_dffcl_data_in1_1755007911602_91),
            .dffcl_data_in2(inj_dffcl_data_in2_1755007911602_999)
        );
        explicit_non_ansi_ports_module explicit_non_ansi_ports_module_inst_1755007911601_9659 (
            .named_conn_in(r_internal_ts1755007911601),
            .named_conn_out(inj_named_conn_out_1755007911601_328),
            .dummy_in_non_ansi(inj_fs_in_target_1755007911600_105),
            .dummy_out_non_ansi(inj_dummy_out_non_ansi_1755007911601_395)
        );
    assign w_internal_ts1755007911601  = reset & inj_fs_in_target_1755007911600_105;
    assign inj_o_wire_out_1755007911600_660  = w_internal_ts1755007911601;
    always_ff @(posedge clk) r_internal_ts1755007911601 <= inj_i_data_sync_1755007911600_884;
    assign inj_o_reg_out_1755007911600_382 = r_internal_ts1755007911601;
    // END: nets_alias_clocking_ts1755007911601

    assign inj_fs_out_target_1755007911600_542 = inj_fs_in_target_1755007911600_105;
    // END: mod_fixup_target_ts1755007911600

    always @* begin
        unique0 casez (inj_case_expr_1755007911600_906)
            2'b1?: inj_internal_out_1755007911600_222 = 8;
            2'b11: inj_internal_out_1755007911600_222 = 9;  
            2'b?1: inj_internal_out_1755007911600_222 = 10; 
            2'b00: inj_internal_out_1755007911600_222 = 11; 
        endcase
    end
    // END: case_unique0_violating_mod_ts1755007911600

    always @(posedge clk) begin
        inj_out_1755007911599_632 <= inj_in_1755007911599_556;
    end
    // END: sequential_always_assign_ts1755007911599

    always_comb begin
        inj_out_res_1755007911599_100 = 1'b0;
        casez (inj_in_val_1755007911599_241)
            3'b1??: inj_out_res_1755007911599_100 = 1'b1;
            3'b0z?: inj_out_res_1755007911599_100 = 1'b0;
            default: inj_out_res_1755007911599_100 = 1'b1;
        endcase
    end
    // END: casez_xz_ts1755007911599
endmodule

