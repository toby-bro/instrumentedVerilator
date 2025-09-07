module another_module_config_dummy (
    input logic i,
    output logic o
);
    assign o = i & i; 
endmodule

module mod_event_implicit (
    input wire [3:0] data_in,
    output reg [3:0] data_out
);
    always @* begin
        data_out = data_in;
    end
endmodule

module module_concat_if (
    input wire [3:0] in_a,
    input wire [3:0] in_b,
    input wire [7:0] in_c,
    input wire in_cond_if,
    output logic [15:0] out_concat,
    output logic [7:0] out_if_else
);
    always_comb begin
    out_concat = {in_a, in_b, in_c};
    if (in_cond_if) begin
        out_if_else = in_c;
    end else begin
        out_if_else = {in_a, in_b};
    end
    end
endmodule

module more_procedural (
    input logic [31:0] p_in1,
    input logic [31:0] p_in2,
    input logic [1:0] p_mode,
    output logic [31:0] p_out
);
    always_comb begin
        case (p_mode)
            2'b00: p_out = (p_in1 + p_in2) * 2;
            2'b01: p_out = (p_in1 - p_in2) / 3; 
            2'b10: p_out = (p_in1 << 4) | (p_in2 >> 2);
            default: p_out = ~(p_in1 ^ p_in2) + 1;
        endcase
    end
endmodule

module split_conditional_reorder (
    input logic clk_cc,
    input logic condition_cc,
    input logic [7:0] val1_cc,
    input logic [7:0] val2_cc,
    input logic [7:0] val3_cc,
    output logic [7:0] out_reg_cc
);
    always @(posedge clk_cc) begin
        out_reg_cc <= val1_cc;
        if (condition_cc) begin
            out_reg_cc <= val2_cc;
        end else begin
            out_reg_cc <= val3_cc;
        end
    end
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

module snippet (
    input wire clk,
    input bit inj_condition_m10_1755007880342_344,
    input logic inj_condition_y_1755007880339_273,
    input bit [7:0] inj_data1_1755007880344_989,
    input bit [7:0] inj_data2_1755007880344_415,
    input wire [3:0] inj_in_a_1755007880341_786,
    input wire [3:0] inj_in_b_1755007880341_48,
    input wire [7:0] inj_in_c_1755007880341_225,
    input integer inj_in_int_1755007880345_698,
    input logic [15:0] inj_in_u16_1755007880345_241,
    input logic [1:0] inj_in_val_1755007880339_609,
    input logic [2:0] inj_in_val_1755007880340_758,
    input logic [7:0] inj_in_val_y_1755007880339_232,
    input logic [31:0] inj_p_in1_1755007880341_446,
    input logic [31:0] inj_p_in2_1755007880341_185,
    input logic [7:0] inj_val2_cc_1755007880340_764,
    input logic [7:0] inj_val3_cc_1755007880340_419,
    input wire reset,
    output reg [3:0] inj_data_out_1755007880346_608,
    output logic inj_o_1755007880347_559,
    output logic [7:0] inj_out2_a_1755007880342_377,
    output logic inj_out_bit_1755007880348_83,
    output logic [15:0] inj_out_concat_1755007880341_975,
    output logic [7:0] inj_out_if_else_1755007880341_213,
    output logic [7:0] inj_out_reg_cc_1755007880340_710,
    output reg inj_out_res_1755007880339_326,
    output reg inj_out_res_1755007880340_402,
    output logic signed [15:0] inj_out_s16_1755007880345_218,
    output logic signed [31:0] inj_out_s32_from_int_1755007880345_399,
    output logic signed [31:0] inj_out_s32_from_l32_1755007880345_355,
    output logic [31:0] inj_out_u32_from_int_1755007880345_482,
    output logic [31:0] inj_out_u32_from_l32_1755007880345_76,
    output logic [7:0] inj_out_u8_1755007880345_949,
    output logic [31:0] inj_out_val_1755007880343_724,
    output logic [7:0] inj_out_val_m10_1755007880342_736,
    output logic [7:0] inj_out_vec_y_1755007880339_444,
    output logic [31:0] inj_p_out_1755007880341_12,
    output bit [7:0] inj_result1_1755007880344_817,
    output bit [7:0] inj_result2_1755007880344_851
);
    // BEGIN: case_default_ts1755007880339
    // BEGIN: casez_xz_ts1755007880340
    // BEGIN: split_basic_nonblocking_ts1755007880342
    // BEGIN: unsupported_cond_expr_ts1755007880342
    logic [7:0] var_m10_ts1755007880342;
        // BEGIN: recursive_macro_dummy_ts1755007880348
        `define RECURSIVE_TEST `RECURSIVE_TEST
        assign inj_out_bit_1755007880348_83 = inj_condition_y_1755007880339_273;
        // END: recursive_macro_dummy_ts1755007880348

        another_module_config_dummy another_module_config_dummy_inst_1755007880347_3254 (
            .i(inj_condition_y_1755007880339_273),
            .o(inj_o_1755007880347_559)
        );
        mod_event_implicit mod_event_implicit_inst_1755007880346_3785 (
            .data_in(inj_in_a_1755007880341_786),
            .data_out(inj_data_out_1755007880346_608)
        );
        // BEGIN: SignedUnsignedConversions_ts1755007880345
        always_comb begin
            inj_out_u8_1755007880345_949 = $unsigned(var_m10_ts1755007880342);
            inj_out_s16_1755007880345_218 = $signed(inj_in_u16_1755007880345_241);
            inj_out_s32_from_l32_1755007880345_355 = $signed(inj_p_in2_1755007880341_185);
            inj_out_u32_from_l32_1755007880345_76 = $unsigned(inj_p_in2_1755007880341_185);
            inj_out_s32_from_int_1755007880345_399 = $signed(inj_in_int_1755007880345_698);
            inj_out_u32_from_int_1755007880345_482 = $unsigned(inj_in_int_1755007880345_698);
        end
        // END: SignedUnsignedConversions_ts1755007880345

        // BEGIN: comb_conditional_ts1755007880344
        always @* begin
            if (inj_condition_m10_1755007880342_344) begin
                inj_result1_1755007880344_817 = inj_data1_1755007880344_989;
                inj_result2_1755007880344_851 = inj_data1_1755007880344_989;
            end else begin
                inj_result1_1755007880344_817 = inj_data2_1755007880344_415;
                inj_result2_1755007880344_851 = inj_data2_1755007880344_415;
            end
        end
        // END: comb_conditional_ts1755007880344

        // BEGIN: member_access_packed_union_ts1755007880343
        typedef union packed {
            logic [31:0] a_ts1755007880343; 
            logic [31:0] b_ts1755007880343; 
        } my_packed_union;
        my_packed_union union_var;
        always_comb begin
            if (inj_condition_m10_1755007880342_344)
                union_var.a_ts1755007880343 = inj_p_in1_1755007880341_446;
            else
                union_var.b_ts1755007880343 = inj_p_in1_1755007880341_446[31:0];
            inj_out_val_1755007880343_724 = union_var.a_ts1755007880343;
        end
        // END: member_access_packed_union_ts1755007880343

    always_comb begin
        var_m10_ts1755007880342 = inj_val3_cc_1755007880340_419;
        inj_out_val_m10_1755007880342_736 = inj_condition_m10_1755007880342_344 ? var_m10_ts1755007880342 : var_m10_ts1755007880342;
        var_m10_ts1755007880342++;
    end
    // END: unsupported_cond_expr_ts1755007880342

    always @(posedge clk) begin
        inj_out2_a_1755007880342_377 <= inj_in_val_y_1755007880339_232;
    end
    // END: split_basic_nonblocking_ts1755007880342

    more_procedural more_procedural_inst_1755007880341_1992 (
        .p_out(inj_p_out_1755007880341_12),
        .p_in1(inj_p_in1_1755007880341_446),
        .p_in2(inj_p_in2_1755007880341_185),
        .p_mode(inj_in_val_1755007880339_609)
    );
    module_concat_if module_concat_if_inst_1755007880341_1805 (
        .out_concat(inj_out_concat_1755007880341_975),
        .out_if_else(inj_out_if_else_1755007880341_213),
        .in_a(inj_in_a_1755007880341_786),
        .in_b(inj_in_b_1755007880341_48),
        .in_c(inj_in_c_1755007880341_225),
        .in_cond_if(clk)
    );
    always_comb begin
        inj_out_res_1755007880340_402 = 1'b0;
        casez (inj_in_val_1755007880340_758)
            3'b1??: inj_out_res_1755007880340_402 = 1'b1;
            3'b0z?: inj_out_res_1755007880340_402 = 1'b0;
            default: inj_out_res_1755007880340_402 = 1'b1;
        endcase
    end
    // END: casez_xz_ts1755007880340

    split_conditional_reorder split_conditional_reorder_inst_1755007880340_2628 (
        .condition_cc(inj_condition_y_1755007880339_273),
        .val1_cc(inj_in_val_y_1755007880339_232),
        .val2_cc(inj_val2_cc_1755007880340_764),
        .val3_cc(inj_val3_cc_1755007880340_419),
        .out_reg_cc(inj_out_reg_cc_1755007880340_710),
        .clk_cc(clk)
    );
    always_comb begin
        inj_out_res_1755007880339_326 = 1'b0;
        case (inj_in_val_1755007880339_609)
            2'b01: inj_out_res_1755007880339_326 = 1'b1;
            2'b10: inj_out_res_1755007880339_326 = 1'b0;
            default: inj_out_res_1755007880339_326 = 1'b1;
        endcase
    end
    // END: case_default_ts1755007880339

    split_vector_assign split_vector_assign_inst_1755007880339_843 (
        .clk_y(clk),
        .condition_y(inj_condition_y_1755007880339_273),
        .in_val_y(inj_in_val_y_1755007880339_232),
        .out_vec_y(inj_out_vec_y_1755007880339_444)
    );
endmodule

