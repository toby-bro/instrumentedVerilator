interface cond_if;
    logic [15:0] control_reg;
    logic [15:0] status_reg;
    modport CtrlStat (output control_reg, input status_reg);
endinterface
module Mod_TernaryLogic (
    input wire [7:0] in_a,
    input wire [7:0] in_b,
    input wire in_bit,
    input wire [7:0] in_c,
    input wire in_cond,
    input wire in_cond_neq_lhs,
    input wire in_cond_neq_rhs,
    input wire in_cond_not,
    input wire [7:0] in_not_else,
    input wire [7:0] in_not_then,
    output logic out_eq,
    output logic out_eq_concat,
    output logic out_gt,
    output logic out_gte,
    output logic out_lt,
    output logic out_lte,
    output logic out_neq,
    output logic out_not_eq,
    output logic out_not_neq,
    output logic out_ternary,
    output logic out_ternary_1bit_0else,
    output logic out_ternary_1bit_0then,
    output logic out_ternary_1bit_1else,
    output logic out_ternary_1bit_1then,
    output logic out_ternary_const_cond_false,
    output logic out_ternary_const_cond_true,
    output logic [7:0] out_ternary_dec,
    output logic [7:0] out_ternary_inc,
    output logic [7:0] out_ternary_pulled_nots,
    output logic out_ternary_swapped_cond,
    output logic out_ternary_swapped_neq_cond
);
    parameter [7:0] CONST_ONE_8 = 8'h01;
    parameter [0:0] CONST_ZERO_1 = 1'b0;
    parameter [0:0] CONST_ONE_1 = 1'b1;
    logic [7:0] intermediate_const_concat_comp;
    logic [15:0] intermediate_concat_comp_src;
    always_comb begin
        out_eq = (in_a == in_b);
        out_neq = (in_a != in_b);
        out_gt = (in_a > in_b);
        out_lt = (in_a < in_b);
        out_gte = (in_a >= in_b);
        out_lte = (in_a <= in_b);
        out_not_eq = !(in_a == in_b);
        out_not_neq = !(in_a != in_b);
        intermediate_const_concat_comp = 8'hAA;
        intermediate_concat_comp_src = {in_a, in_b};
        out_eq_concat = (intermediate_const_concat_comp == intermediate_concat_comp_src[7:0]);
        out_ternary = in_cond ? in_a[0] : in_b[0];
        out_ternary_const_cond_true = 1'b1 ? in_a[0] : in_b[0];
        out_ternary_const_cond_false = 1'b0 ? in_a[0] : in_b[0];
        out_ternary_swapped_cond = !in_cond_not ? in_a[0] : in_b[0];
        out_ternary_swapped_neq_cond = (in_cond_neq_lhs != in_cond_neq_rhs) ? in_a[0] : in_b[0];
        out_ternary_pulled_nots = in_cond ? ~in_not_then : ~in_not_else;
        out_ternary_inc = in_cond ? (in_a + CONST_ONE_8) : in_a;
        out_ternary_dec = in_cond ? (in_a - CONST_ONE_8) : in_a;
        out_ternary_1bit_0then = in_cond ? CONST_ZERO_1 : in_bit;
        out_ternary_1bit_1then = in_cond ? CONST_ONE_1 : in_bit;
        out_ternary_1bit_0else = in_cond ? in_bit : CONST_ZERO_1;
        out_ternary_1bit_1else = in_cond ? in_bit : CONST_ONE_1;
    end
endmodule

module ReductionOperations (
    input logic [7:0] data_in,
    output logic and_reduce,
    output logic or_reduce,
    output logic xor_reduce
);
    assign and_reduce = &data_in;
    assign or_reduce = |data_in;
    assign xor_reduce = ^data_in;
endmodule

module SimpleAssign (
    input logic [9:0] val_in,
    output logic [9:0] val_out
);
    assign val_out = val_in;
endmodule

module member_access_packed_union (
    input logic [31:0] in_val,
    input bit select_a,
    output logic [31:0] out_val
);
    typedef union packed {
        logic [31:0] a; 
        logic [31:0] b; 
    } my_packed_union;
    my_packed_union union_var;
    always_comb begin
        if (select_a)
            union_var.a = in_val;
        else
            union_var.b = in_val[31:0];
        out_val = union_var.a;
    end
endmodule

module module_using_package_param (
    input logic [31:0] wide_data_in,
    output logic [31:0] wide_data_out
);
    assign wide_data_out = wide_data_in;
endmodule

module split_multiple_blocking (
    input logic [3:0] data_in_n,
    output logic [3:0] data_out1_n,
    output logic [3:0] data_out2_n
);
    logic [3:0] temp_n;
    always @(*) begin
        temp_n = data_in_n + 1;
        data_out1_n = temp_n * 2;
        data_out2_n = temp_n + 3;
    end
endmodule

module unpacked_array_module (
    input wire [7:0] in_array_data,
    input wire [1:0] select_idx,
    output wire [3:0] out_element
);
    logic [3:0] data_array [4];
    always @(*) begin
        data_array[0] = in_array_data[3:0];
        data_array[1] = in_array_data[7:4];
        data_array[2] = 4'd8;
        data_array[3] = 4'd12;
    end
    assign out_element = data_array[select_idx];
endmodule

module snippet (
    input wire clk,
    input logic [15:0] inj_data_in_1755007752132_124,
    input logic [3:0] inj_i_addr_arr_1755007752119_953,
    input logic [3:0] inj_i_addr_sel_1755007752119_842,
    input logic [7:0] inj_in1_1755007752118_653,
    input logic [7:0] inj_in2_1755007752118_255,
    input wire [7:0] inj_in_a_1755007752117_235,
    input wire [7:0] inj_in_b_1755007752117_666,
    input wire inj_in_bit_1755007752117_347,
    input wire [7:0] inj_in_c_1755007752117_622,
    input wire inj_in_cond_1755007752117_308,
    input wire inj_in_cond_neq_rhs_1755007752117_839,
    input wire [7:0] inj_in_not_else_1755007752117_106,
    input wire [7:0] inj_in_not_then_1755007752117_520,
    input logic [31:0] inj_in_val_1755007752121_71,
    input int inj_in_val_1755007752124_174,
    input logic inj_p1_1755007752122_949,
    input bit inj_select_a_1755007752121_519,
    input wire [1:0] inj_select_idx_1755007752137_101,
    input logic [9:0] inj_val_in_1755007752126_573,
    input wire reset,
    output logic inj_and_reduce_1755007752123_902,
    output logic inj_control_status_1755007752132_368,
    output logic [3:0] inj_data_out1_n_1755007752120_201,
    output logic [3:0] inj_data_out2_n_1755007752120_900,
    output logic [7:0] inj_o_array_var_elem_1755007752119_960,
    output logic inj_o_bind_status_1755007752131_44,
    output logic inj_o_sel_var_bit_1755007752119_101,
    output logic [7:0] inj_o_target_result_1755007752129_521,
    output logic inj_or_reduce_1755007752123_206,
    output logic [7:0] inj_out1_1755007752118_824,
    output logic [15:0] inj_out_concat_1755007752127_840,
    output wire [3:0] inj_out_element_1755007752137_160,
    output logic inj_out_eq_1755007752117_144,
    output logic inj_out_eq_concat_1755007752117_323,
    output logic inj_out_gt_1755007752117_873,
    output logic inj_out_gte_1755007752117_825,
    output logic inj_out_lt_1755007752117_257,
    output logic inj_out_lte_1755007752117_875,
    output logic inj_out_neq_1755007752117_870,
    output logic inj_out_not_eq_1755007752117_604,
    output logic inj_out_not_neq_1755007752117_948,
    output logic inj_out_ternary_1755007752117_856,
    output logic inj_out_ternary_1bit_0else_1755007752117_30,
    output logic inj_out_ternary_1bit_0then_1755007752117_330,
    output logic inj_out_ternary_1bit_1else_1755007752117_478,
    output logic inj_out_ternary_1bit_1then_1755007752117_645,
    output logic inj_out_ternary_const_cond_false_1755007752117_250,
    output logic inj_out_ternary_const_cond_true_1755007752117_133,
    output logic [7:0] inj_out_ternary_dec_1755007752117_341,
    output logic [7:0] inj_out_ternary_inc_1755007752117_842,
    output logic [7:0] inj_out_ternary_pulled_nots_1755007752117_191,
    output logic inj_out_ternary_swapped_cond_1755007752117_336,
    output logic inj_out_ternary_swapped_neq_cond_1755007752117_762,
    output logic [31:0] inj_out_val_1755007752121_715,
    output int inj_out_val_1755007752124_39,
    output logic inj_p2_1755007752122_973,
    output logic inj_reset_1755007752139_42,
    output logic [9:0] inj_val_out_1755007752126_334,
    output logic [31:0] inj_wide_data_out_1755007752136_663,
    output logic inj_xor_reduce_1755007752123_68
);
    // BEGIN: basic_comb_ts1755007752118
    ;
    logic [7:0] temp_wire_ts1755007752118;
        // BEGIN: HandleOutOfBoundsRead_ts1755007752119
        parameter ARR_SIZE = 4;
        logic [7:0] my_array_ts1755007752119 [0:ARR_SIZE-1];
            // BEGIN: child_empty_ports_ts1755007752122
            input logic inj_p1_1755007752122_949_ts1755007752122;
            output logic inj_p2_1755007752122_973_ts1755007752122;
                // BEGIN: cu_timeunit_mod_ts1755007752139
                logic internal_sig_ts1755007752139;
                always_ff @(posedge clk) begin
                    inj_reset_1755007752139_42 <= 1'b0;
                    internal_sig_ts1755007752139 = clk;
                end
                // END: cu_timeunit_mod_ts1755007752139

                unpacked_array_module unpacked_array_module_inst_1755007752137_2427 (
                    .select_idx(inj_select_idx_1755007752137_101),
                    .out_element(inj_out_element_1755007752137_160),
                    .in_array_data(inj_in_c_1755007752117_622)
                );
                module_using_package_param module_using_package_param_inst_1755007752136_9984 (
                    .wide_data_out(inj_wide_data_out_1755007752136_663),
                    .wide_data_in(inj_in_val_1755007752121_71)
                );
                // BEGIN: module_conditional_write_ts1755007752133
                cond_if cif_inst();
                always_comb begin
                    if (inj_p1_1755007752122_949) begin
                        cif_inst.control_reg = inj_data_in_1755007752132_124;
                    end else begin
                        cif_inst.control_reg = 16'h0;
                    end
                    inj_control_status_1755007752132_368 = (cif_inst.control_reg != 16'h0);
                end
                // END: module_conditional_write_ts1755007752133

                // BEGIN: module_to_bind_ts1755007752131
                always_comb inj_o_bind_status_1755007752131_44 = |inj_i_addr_sel_1755007752119_842;
                // END: module_to_bind_ts1755007752131

                // BEGIN: target_module_for_bind_ts1755007752129
                always_comb inj_o_target_result_1755007752129_521 = inj_in1_1755007752118_653 + 1;
                // END: target_module_for_bind_ts1755007752129

                // BEGIN: ConcatVectorOps_ts1755007752127
                assign inj_out_concat_1755007752127_840 = {inj_i_addr_arr_1755007752119_953, inj_i_addr_sel_1755007752119_842, temp_wire_ts1755007752118};
                // END: ConcatVectorOps_ts1755007752127

                SimpleAssign SimpleAssign_inst_1755007752126_7765 (
                    .val_out(inj_val_out_1755007752126_334),
                    .val_in(inj_val_in_1755007752126_573)
                );
                // BEGIN: invalid_this_diag_mod_ts1755007752125
                assign inj_out_val_1755007752124_39 = inj_in_val_1755007752124_174;
                // END: invalid_this_diag_mod_ts1755007752125

                ReductionOperations ReductionOperations_inst_1755007752123_7330 (
                    .data_in(my_array_ts1755007752119),
                    .and_reduce(inj_and_reduce_1755007752123_902),
                    .or_reduce(inj_or_reduce_1755007752123_206),
                    .xor_reduce(inj_xor_reduce_1755007752123_68)
                );
            assign inj_p2_1755007752122_973_ts1755007752122 = inj_p1_1755007752122_949_ts1755007752122;
            // END: child_empty_ports_ts1755007752122

            member_access_packed_union member_access_packed_union_inst_1755007752121_405 (
                .out_val(inj_out_val_1755007752121_715),
                .in_val(inj_in_val_1755007752121_71),
                .select_a(inj_select_a_1755007752121_519)
            );
            split_multiple_blocking split_multiple_blocking_inst_1755007752120_6560 (
                .data_in_n(inj_i_addr_sel_1755007752119_842),
                .data_out1_n(inj_data_out1_n_1755007752120_201),
                .data_out2_n(inj_data_out2_n_1755007752120_900)
            );
        assign my_array_ts1755007752119[0] = 8'd10;
        assign my_array_ts1755007752119[1] = 8'd20;
        assign my_array_ts1755007752119[2] = 8'd30;
        assign my_array_ts1755007752119[3] = 8'd40;
        assign inj_o_sel_var_bit_1755007752119_101 = inj_in2_1755007752118_255[inj_i_addr_sel_1755007752119_842];
        assign inj_o_array_var_elem_1755007752119_960 = my_array_ts1755007752119[inj_i_addr_arr_1755007752119_953];
        // END: HandleOutOfBoundsRead_ts1755007752119

    assign temp_wire_ts1755007752118 = inj_in1_1755007752118_653 + inj_in2_1755007752118_255;
    always_comb begin
        inj_out1_1755007752118_824 = temp_wire_ts1755007752118;
    end
    // END: basic_comb_ts1755007752118

    Mod_TernaryLogic Mod_TernaryLogic_inst_1755007752118_9065 (
        .out_ternary_1bit_0then(inj_out_ternary_1bit_0then_1755007752117_330),
        .out_not_eq(inj_out_not_eq_1755007752117_604),
        .out_not_neq(inj_out_not_neq_1755007752117_948),
        .in_a(inj_in_a_1755007752117_235),
        .out_ternary_const_cond_false(inj_out_ternary_const_cond_false_1755007752117_250),
        .out_eq(inj_out_eq_1755007752117_144),
        .out_ternary(inj_out_ternary_1755007752117_856),
        .out_ternary_inc(inj_out_ternary_inc_1755007752117_842),
        .out_lte(inj_out_lte_1755007752117_875),
        .out_gte(inj_out_gte_1755007752117_825),
        .in_cond(inj_in_cond_1755007752117_308),
        .in_not_then(inj_in_not_then_1755007752117_520),
        .out_lt(inj_out_lt_1755007752117_257),
        .in_cond_not(clk),
        .in_cond_neq_rhs(inj_in_cond_neq_rhs_1755007752117_839),
        .out_neq(inj_out_neq_1755007752117_870),
        .out_ternary_swapped_cond(inj_out_ternary_swapped_cond_1755007752117_336),
        .out_ternary_swapped_neq_cond(inj_out_ternary_swapped_neq_cond_1755007752117_762),
        .out_ternary_1bit_1else(inj_out_ternary_1bit_1else_1755007752117_478),
        .out_eq_concat(inj_out_eq_concat_1755007752117_323),
        .out_ternary_1bit_0else(inj_out_ternary_1bit_0else_1755007752117_30),
        .out_gt(inj_out_gt_1755007752117_873),
        .in_b(inj_in_b_1755007752117_666),
        .in_cond_neq_lhs(reset),
        .out_ternary_pulled_nots(inj_out_ternary_pulled_nots_1755007752117_191),
        .in_c(inj_in_c_1755007752117_622),
        .in_bit(inj_in_bit_1755007752117_347),
        .in_not_else(inj_in_not_else_1755007752117_106),
        .out_ternary_1bit_1then(inj_out_ternary_1bit_1then_1755007752117_645),
        .out_ternary_const_cond_true(inj_out_ternary_const_cond_true_1755007752117_133),
        .out_ternary_dec(inj_out_ternary_dec_1755007752117_341)
    );
endmodule

