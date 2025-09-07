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

module BitwiseAssign (
    input logic [3:0] in_a,
    input logic [3:0] in_b,
    output logic [3:0] out_y
);
    assign out_y = in_a ^ in_b;
endmodule

module CoverageHelper (
    input bit in_h,
    output logic out_h
);
    assign out_h = in_h;
endmodule

module ModuleBasic (
    input logic a,
    input int b,
    output logic out_a,
    output int out_b
);
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c;
    int   d;
    always_comb begin
        logic temp_v;
        temp_v = d;
        c      = temp_v;
    end
    assign out_a = a;
    assign d     = b;
    assign out_b = d + P1 + LP1;
endmodule

module Module_ConfigKeywords (
    input bit cfg_in,
    output bit cfg_out
);
    assign cfg_out = cfg_in;
endmodule

module SimpleLogicTest (
    input bit [7:0] data_in,
    input bit select_signal,
    output bit [7:0] data_out
);
    logic [7:0] temp_data;
    always_comb begin
        if (select_signal) begin
            temp_data = data_in + 1;
        end else begin
            temp_data = data_in - 1;
        end
        data_out = temp_data;
    end
endmodule

module StructExample (
    input logic [15:0] in_data,
    output logic [7:0] out_field_a,
    output logic [7:0] out_field_b
);
    typedef struct packed {
        logic [7:0] field_a;
        logic [7:0] field_b;
    } example_struct_t;
    example_struct_t my_struct;
    always_comb begin
        my_struct     = in_data;
        out_field_a   = my_struct.field_a;
        out_field_b   = my_struct.field_b;
    end
endmodule

module arith_comp_ops (
    input logic [15:0] in1,
    input logic [15:0] in2,
    input logic [15:0] in3,
    input logic [15:0] in4,
    input logic [15:0] in5,
    output logic out
);
    assign out = (in1 + in2) * in3 > in4 - in5;
endmodule

module child_scalar_port (
    input logic data_in,
    output logic data_out
);
    assign data_out = data_in;
endmodule

module assign_pattern_lvalue (
    input logic [38:0] in_packed_for_conv,
    input logic [7:0] in_vec,
    output logic out_bit_conv,
    output int out_int_conv,
    output logic [7:0] out_unpacked_struct_repacked,
    output logic [5:0] out_vec_conv
);
    eight_bit_unpacked_struct_t unpacked_s;
    logic [7:0] reg_unpacked_struct_repacked;
    int int_var;
    logic bit_var;
    logic [5:0] vec_var;
    always_comb begin
        unpacked_s.f1 = in_vec[3:0];
        unpacked_s.f2 = in_vec[4];
        unpacked_s.f3 = in_vec[7:5];
        reg_unpacked_struct_repacked = { unpacked_s.f3, unpacked_s.f2, unpacked_s.f1 };
        int_var = in_packed_for_conv[31:0];
        bit_var = in_packed_for_conv[32];
        vec_var = in_packed_for_conv[38:33];
        out_unpacked_struct_repacked = reg_unpacked_struct_repacked;
        out_int_conv = int_var;
        out_bit_conv = bit_var;
        out_vec_conv = vec_var;
    end
endmodule

module mod_casex_wildcard_overlap_priority (
    input bit [3:0] in_mask_x,
    output bit [1:0] out_match_type_x
);
always_comb begin
    out_match_type_x = 2'b01;
    priority casex (in_mask_x)
        4'b1X0Z: begin
            out_match_type_x = 2'b10;
        end
        4'b10?Z: begin
            out_match_type_x = 2'b11;
        end
        4'bZ1?X: begin
            out_match_type_x = 2'b00;
        end
        default: begin
            out_match_type_x = 2'b01;
        end
    endcase
end
endmodule

module simple_logic_b (
    input wire data_c,
    output wire data_d
);
    assign data_d = data_c;
endmodule

module split_vector_assign (
    input logic clk_y,
    input logic condition_y,
    input logic [7:0] in_val_y,
    output logic [7:0] out_vec_y
);
    always @(posedge clk_y) begin
        if (condition_y) begin
            out_vec_y[3:0] <= in_val_y[3:0];
            out_vec_y[7:4] <= in_val_y[7:4] + 1;
        end else begin
            out_vec_y <= 8'hFF;
        end
    end
endmodule

module snippet #(
    parameter int SEL_PARAM = 6
) (
    input wire clk,
    input logic [3:0] inj_case_inside_val_1755007852216_228,
    input bit inj_cfg_in_1755007852216_112,
    input logic [7:0] inj_d1_w_1755007852262_202,
    input logic [7:0] inj_d2_w_1755007852262_360,
    input logic [7:0] inj_d3_w_1755007852262_677,
    input bit [7:0] inj_data_in_1755007852222_624,
    input logic inj_dummy_in_1755007852218_6,
    input logic [15:0] inj_in1_1755007852251_747,
    input logic [15:0] inj_in2_1755007852251_528,
    input logic [7:0] inj_in2_a_1755007852217_495,
    input logic [15:0] inj_in4_1755007852251_206,
    input logic [15:0] inj_in5_1755007852251_239,
    input wire [7:0] inj_in_a_1755007852231_826,
    input logic [3:0] inj_in_b_1755007852220_689,
    input wire [7:0] inj_in_b_1755007852231_36,
    input wire [7:0] inj_in_c_1755007852231_82,
    input wire [7:0] inj_in_const1_1755007852231_61,
    input wire [7:0] inj_in_const2_1755007852231_16,
    input logic [15:0] inj_in_data_1755007852240_671,
    input bit [3:0] inj_in_mask_x_1755007852259_580,
    input wire [15:0] inj_in_packed_data_1755007852218_225,
    input logic [38:0] inj_in_packed_for_conv_1755007852223_79,
    input logic [31:0] inj_in_val_1755007852227_844,
    input int inj_sel_in_1755007852228_242,
    input logic [1:0] inj_sel_w_1755007852262_59,
    input logic inj_vif_valid_1755007852217_913,
    input wire reset,
    output bit inj_cfg_out_1755007852216_425,
    output bit inj_cfg_out_1755007852224_894,
    output wire inj_data_b_1755007852245_304,
    output wire inj_data_d_1755007852221_434,
    output bit [7:0] inj_data_out_1755007852222_967,
    output logic [7:0] inj_data_out_1755007852228_321,
    output logic inj_data_out_1755007852265_649,
    output logic inj_dummy_out_1755007852217_582,
    output logic [4:0] inj_internal_out_1755007852216_160,
    output logic inj_o_1755007852226_267,
    output logic [7:0] inj_out2_a_1755007852217_829,
    output logic inj_out_1755007852251_9,
    output logic [7:0] inj_out_add_assoc_1755007852231_150,
    output logic [7:0] inj_out_and_assoc_1755007852231_776,
    output logic [7:0] inj_out_and_swap_const_1755007852231_559,
    output logic [7:0] inj_out_arith_1755007852231_5,
    output logic inj_out_bit_conv_1755007852223_669,
    output logic [7:0] inj_out_bitwise_1755007852231_402,
    output wire [7:0] inj_out_byte_1755007852218_464,
    output logic [7:0] inj_out_data_1755007852217_642,
    output logic [7:0] inj_out_field_a_1755007852240_533,
    output logic [7:0] inj_out_field_b_1755007852240_444,
    output logic inj_out_h_1755007852216_681,
    output logic inj_out_h_1755007852217_601,
    output logic inj_out_h_1755007852253_747,
    output int inj_out_int_conv_1755007852223_406,
    output logic inj_out_logical_1755007852231_919,
    output bit [1:0] inj_out_match_type_x_1755007852259_524,
    output logic [7:0] inj_out_mul_assoc_1755007852231_926,
    output logic [7:0] inj_out_negate_1755007852231_866,
    output logic [7:0] inj_out_or_assoc_1755007852231_298,
    output logic [7:0] inj_out_or_swap_not_1755007852231_239,
    output logic inj_out_sub_1755007852225_227,
    output logic [7:0] inj_out_sum_1755007852219_791,
    output logic [7:0] inj_out_unary_not_1755007852231_289,
    output logic [7:0] inj_out_unpacked_struct_repacked_1755007852223_767,
    output logic [31:0] inj_out_val_1755007852227_618,
    output logic inj_out_valid_1755007852217_410,
    output logic [7:0] inj_out_vec_1755007852219_817,
    output logic [5:0] inj_out_vec_conv_1755007852223_33,
    output logic [7:0] inj_out_vec_y_1755007852256_902,
    output logic [7:0] inj_out_w_1755007852262_207,
    output logic [7:0] inj_out_xor_assoc_1755007852231_792,
    output logic [7:0] inj_out_xor_swap_var_1755007852231_464,
    output logic [3:0] inj_out_y_1755007852220_281,
    output logic [3:0] inj_result_1755007852242_63,
    output logic inj_unused_out_1755007852248_512
);
    // BEGIN: Module_ConfigKeywords_ts1755007852216
    // BEGIN: CoverageHelper_ts1755007852216
    // BEGIN: case_parallel_simple_mod_ts1755007852217
    // BEGIN: split_basic_nonblocking_ts1755007852217
    // BEGIN: virtual_interface_lookup_mod_ts1755007852218
    // BEGIN: packed_struct_module_ts1755007852218
    typedef struct packed {
        logic [7:0] byte1_ts1755007852218;
        logic [7:0] byte2_ts1755007852218;
    } my_packed_struct_t;
    my_packed_struct_t data_struct;
    // BEGIN: simple_for_loop_ts1755007852220
    logic [7:0] sum_ts1755007852220;
    // BEGIN: member_access_packed_union_ts1755007852227
    typedef union packed {
        logic [31:0] a_ts1755007852227; 
        logic [31:0] b_ts1755007852227; 
    } my_packed_union;
    my_packed_union union_var;
    // BEGIN: Mod_BasicOps_ts1755007852237
    logic [7:0] intermediate_arith_ts1755007852235;
    logic [7:0] intermediate_bitwise_ts1755007852235;
    logic [0:0] intermediate_logical_ts1755007852235;
    logic [7:0] intermediate_add_assoc_ts1755007852235;
    logic [7:0] intermediate_mul_assoc_ts1755007852235;
    logic [7:0] intermediate_and_assoc_ts1755007852235;
    logic [7:0] intermediate_or_assoc_ts1755007852235;
    logic [7:0] intermediate_xor_assoc_ts1755007852235;
    parameter [7:0] CONST_ZERO = 8'h00;
    child_scalar_port child_scalar_port_inst_1755007852265_8007 (
        .data_in(inj_vif_valid_1755007852217_913),
        .data_out(inj_data_out_1755007852265_649)
    );
    // BEGIN: split_case_ts1755007852262
    always @(posedge clk) begin
        case (inj_sel_w_1755007852262_59)
            2'b00: inj_out_w_1755007852262_207 <= inj_in2_a_1755007852217_495;
            2'b01: inj_out_w_1755007852262_207 <= inj_d1_w_1755007852262_202;
            2'b10: inj_out_w_1755007852262_207 <= inj_d2_w_1755007852262_360;
            default: inj_out_w_1755007852262_207 <= inj_d3_w_1755007852262_677;
        endcase
    end
    // END: split_case_ts1755007852262

    mod_casex_wildcard_overlap_priority mod_casex_wildcard_overlap_priority_inst_1755007852259_8555 (
        .in_mask_x(inj_in_mask_x_1755007852259_580),
        .out_match_type_x(inj_out_match_type_x_1755007852259_524)
    );
    split_vector_assign split_vector_assign_inst_1755007852256_6025 (
        .condition_y(inj_vif_valid_1755007852217_913),
        .in_val_y(inj_in2_a_1755007852217_495),
        .out_vec_y(inj_out_vec_y_1755007852256_902),
        .clk_y(clk)
    );
    CoverageHelper CoverageHelper_inst_1755007852253_9775 (
        .in_h(inj_cfg_in_1755007852216_112),
        .out_h(inj_out_h_1755007852253_747)
    );
    arith_comp_ops arith_comp_ops_inst_1755007852251_4405 (
        .in1(inj_in1_1755007852251_747),
        .in2(inj_in2_1755007852251_528),
        .in3(inj_in_data_1755007852240_671),
        .in4(inj_in4_1755007852251_206),
        .in5(inj_in5_1755007852251_239),
        .out(inj_out_1755007852251_9)
    );
    // BEGIN: unreferenced_module_ts1755007852248
    assign inj_unused_out_1755007852248_512 = ~inj_dummy_in_1755007852218_6;
    // END: unreferenced_module_ts1755007852248

    // BEGIN: simple_logic_a_ts1755007852245
    assign inj_data_b_1755007852245_304 = ~reset;
    // END: simple_logic_a_ts1755007852245

    // BEGIN: CombinationalLogic_ts1755007852242
    always_comb begin
        if (inj_vif_valid_1755007852217_913) begin
            inj_result_1755007852242_63 = inj_in_b_1755007852220_689 + inj_case_inside_val_1755007852216_228;
        end else begin
            inj_result_1755007852242_63 = 4'h0;
        end
    end
    // END: CombinationalLogic_ts1755007852242

    StructExample StructExample_inst_1755007852240_1845 (
        .in_data(inj_in_data_1755007852240_671),
        .out_field_a(inj_out_field_a_1755007852240_533),
        .out_field_b(inj_out_field_b_1755007852240_444)
    );
    always_comb begin
        intermediate_arith_ts1755007852235 = inj_in_a_1755007852231_826;
        intermediate_arith_ts1755007852235 = intermediate_arith_ts1755007852235 + inj_in_b_1755007852231_36;
        intermediate_arith_ts1755007852235 = intermediate_arith_ts1755007852235 - inj_in_c_1755007852231_82;
        intermediate_arith_ts1755007852235 = intermediate_arith_ts1755007852235 * inj_in_const1_1755007852231_61;
        if (inj_in_b_1755007852231_36 != CONST_ZERO) begin
            intermediate_arith_ts1755007852235 = intermediate_arith_ts1755007852235 / inj_in_b_1755007852231_36;
            intermediate_arith_ts1755007852235 = intermediate_arith_ts1755007852235 % inj_in_b_1755007852231_36;
        end else begin
            intermediate_arith_ts1755007852235 = 'x;
        end
        inj_out_arith_1755007852231_5 = intermediate_arith_ts1755007852235;
        intermediate_bitwise_ts1755007852235 = inj_in_a_1755007852231_826;
        intermediate_bitwise_ts1755007852235 = intermediate_bitwise_ts1755007852235 & inj_in_b_1755007852231_36;
        intermediate_bitwise_ts1755007852235 = intermediate_bitwise_ts1755007852235 | inj_in_c_1755007852231_82;
        intermediate_bitwise_ts1755007852235 = intermediate_bitwise_ts1755007852235 ^ inj_in_const1_1755007852231_61;
        inj_out_bitwise_1755007852231_402 = intermediate_bitwise_ts1755007852235;
        intermediate_logical_ts1755007852235 = (inj_in_a_1755007852231_826 != CONST_ZERO) && (inj_in_b_1755007852231_36 != CONST_ZERO);
        intermediate_logical_ts1755007852235 = intermediate_logical_ts1755007852235 || (inj_in_c_1755007852231_82 != CONST_ZERO);
        inj_out_logical_1755007852231_919 = !intermediate_logical_ts1755007852235;
        inj_out_unary_not_1755007852231_289 = ~inj_in_a_1755007852231_826;
        inj_out_negate_1755007852231_866 = -inj_in_a_1755007852231_826;
        intermediate_add_assoc_ts1755007852235 = (inj_in_a_1755007852231_826 + inj_in_b_1755007852231_36) + inj_in_c_1755007852231_82;
        inj_out_add_assoc_1755007852231_150 = intermediate_add_assoc_ts1755007852235;
        intermediate_mul_assoc_ts1755007852235 = (inj_in_a_1755007852231_826 * inj_in_b_1755007852231_36) * inj_in_c_1755007852231_82;
        inj_out_mul_assoc_1755007852231_926 = intermediate_mul_assoc_ts1755007852235;
        intermediate_and_assoc_ts1755007852235 = (inj_in_a_1755007852231_826 & inj_in_b_1755007852231_36) & inj_in_c_1755007852231_82;
        inj_out_and_assoc_1755007852231_776 = intermediate_and_assoc_ts1755007852235;
        intermediate_or_assoc_ts1755007852235 = (inj_in_a_1755007852231_826 | inj_in_b_1755007852231_36) | inj_in_c_1755007852231_82;
        inj_out_or_assoc_1755007852231_298 = intermediate_or_assoc_ts1755007852235;
        intermediate_xor_assoc_ts1755007852235 = (inj_in_a_1755007852231_826 ^ inj_in_b_1755007852231_36) ^ inj_in_c_1755007852231_82;
        inj_out_xor_assoc_1755007852231_792 = intermediate_xor_assoc_ts1755007852235;
        inj_out_and_swap_const_1755007852231_559 = inj_in_const1_1755007852231_61 & inj_in_a_1755007852231_826;
        inj_out_or_swap_not_1755007852231_239 = (~inj_in_a_1755007852231_826) | inj_in_b_1755007852231_36;
        inj_out_xor_swap_var_1755007852231_464 = inj_in_b_1755007852231_36 ^ inj_in_c_1755007852231_82;
    end
    // END: Mod_BasicOps_ts1755007852237

    // BEGIN: ModuleHierarchy_High_ts1755007852229
    ModuleBasic m1 (
        .a      (1'b1),
        .b      (inj_sel_in_1755007852228_242),
        .out_a  (),
        .out_b  ( )
    );
    if (SEL_PARAM > 5) begin : gen_high
        int high_data_ts1755007852229;
        ModuleBasic m_high (
            .a      (1'b0),
            .b      (SEL_PARAM),
            .out_a  (),
            .out_b  (high_data_ts1755007852229)
        );
    end else begin : gen_low
        int low_data_ts1755007852229;
        ModuleBasic m_low (
            .a      (1'b0),
            .b      (SEL_PARAM),
            .out_a  (),
            .out_b  (low_data_ts1755007852229)
        );
    end
    for (genvar i = 0; i < 2; ++i) begin : gen_loop
        logic [1:0] sub_in_ts1755007852229;
        assign sub_in_ts1755007852229 = inj_in_b_1755007852220_689[i*2 +: 2];
        int temp_int_ts1755007852229;
        ModuleBasic m_inst (
            .a      (1'b0),
            .b      (int'(sub_in_ts1755007852229)),
            .out_a  (),
            .out_b  (temp_int_ts1755007852229)
        );
        assign inj_data_out_1755007852228_321[i*4 +: 4] = temp_int_ts1755007852229[3:0];
    end
    // END: ModuleHierarchy_High_ts1755007852229

    always_comb begin
        if (inj_cfg_in_1755007852216_112)
            union_var.a_ts1755007852227 = inj_in_val_1755007852227_844;
        else
            union_var.b_ts1755007852227 = inj_in_val_1755007852227_844[31:0];
        inj_out_val_1755007852227_618 = union_var.a_ts1755007852227;
    end
    // END: member_access_packed_union_ts1755007852227

    // BEGIN: child_module_v1_config_dummy_ts1755007852226
    assign inj_o_1755007852226_267 = ~inj_dummy_in_1755007852218_6; 
    // END: child_module_v1_config_dummy_ts1755007852226

    // BEGIN: mod_sub_ts1755007852225
    assign inj_out_sub_1755007852225_227 = reset;
    // END: mod_sub_ts1755007852225

    Module_ConfigKeywords Module_ConfigKeywords_inst_1755007852224_1155 (
        .cfg_in(inj_cfg_in_1755007852216_112),
        .cfg_out(inj_cfg_out_1755007852224_894)
    );
    assign_pattern_lvalue assign_pattern_lvalue_inst_1755007852223_6325 (
        .in_vec(inj_in2_a_1755007852217_495),
        .out_bit_conv(inj_out_bit_conv_1755007852223_669),
        .out_int_conv(inj_out_int_conv_1755007852223_406),
        .out_unpacked_struct_repacked(inj_out_unpacked_struct_repacked_1755007852223_767),
        .out_vec_conv(inj_out_vec_conv_1755007852223_33),
        .in_packed_for_conv(inj_in_packed_for_conv_1755007852223_79)
    );
    SimpleLogicTest SimpleLogicTest_inst_1755007852222_9111 (
        .data_in(inj_data_in_1755007852222_624),
        .select_signal(inj_cfg_in_1755007852216_112),
        .data_out(inj_data_out_1755007852222_967)
    );
    simple_logic_b simple_logic_b_inst_1755007852221_6432 (
        .data_d(inj_data_d_1755007852221_434),
        .data_c(clk)
    );
    BitwiseAssign BitwiseAssign_inst_1755007852220_2323 (
        .in_a(inj_case_inside_val_1755007852216_228),
        .in_b(inj_in_b_1755007852220_689),
        .out_y(inj_out_y_1755007852220_281)
    );
    always_comb begin
        sum_ts1755007852220 = 8'h00;
        for (int i = 0; i < 5; i = i + 1) begin
            sum_ts1755007852220 = sum_ts1755007852220 + inj_in2_a_1755007852217_495;
        end
        inj_out_sum_1755007852219_791 = sum_ts1755007852220;
    end
    // END: simple_for_loop_ts1755007852220

    // BEGIN: SimpleLoopExample_ts1755007852219
    always_comb begin
        for (int i = 0; i < 8; i++) begin
            inj_out_vec_1755007852219_817[i] = inj_in2_a_1755007852217_495[7 - i];
        end
    end
    // END: SimpleLoopExample_ts1755007852219

    assign data_struct = inj_in_packed_data_1755007852218_225;
    assign inj_out_byte_1755007852218_464 = data_struct.byte1_ts1755007852218;
    // END: packed_struct_module_ts1755007852218

    always_comb begin
        inj_out_data_1755007852217_642  = inj_in2_a_1755007852217_495;
        inj_out_valid_1755007852217_410 = inj_vif_valid_1755007852217_913;
        inj_dummy_out_1755007852217_582 = inj_dummy_in_1755007852218_6;
    end
    // END: virtual_interface_lookup_mod_ts1755007852218

    CoverageHelper CoverageHelper_inst_1755007852217_3038 (
        .in_h(inj_cfg_in_1755007852216_112),
        .out_h(inj_out_h_1755007852217_601)
    );
    always @(posedge clk) begin
        inj_out2_a_1755007852217_829 <= inj_in2_a_1755007852217_495;
    end
    // END: split_basic_nonblocking_ts1755007852217

    always @* begin
        (* parallel *)
        case (inj_case_inside_val_1755007852216_228)
            4'd0, 4'd1: inj_internal_out_1755007852216_160 = 14;
            4'd2, 4'd3: inj_internal_out_1755007852216_160 = 15;
            default: inj_internal_out_1755007852216_160 = 18;
        endcase
    end
    // END: case_parallel_simple_mod_ts1755007852217

    assign inj_out_h_1755007852216_681 = inj_cfg_in_1755007852216_112;
    // END: CoverageHelper_ts1755007852216

    assign inj_cfg_out_1755007852216_425 = inj_cfg_in_1755007852216_112;
    // END: Module_ConfigKeywords_ts1755007852216
endmodule

