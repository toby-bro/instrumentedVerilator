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

module CoverageHelper (
    input bit in_h,
    output logic out_h
);
    assign out_h = in_h;
endmodule

module LintAsyncFovIssue (
    input logic clk,
    input logic in_h,
    input logic rst_n,
    output logic out_i
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            out_i <= 1'b0;
        end else begin
            out_i <= in_h & out_i;
        end
    end
endmodule

module PackedStructOps (
    input logic [7:0] byte_val,
    input logic [15:0] packed_in,
    output logic [7:0] byte_out,
    output logic [15:0] packed_out
);
    typedef struct packed {
        logic [7:0] low;
        logic [7:0] high;
    } pair_t;
    pair_t data_pair;
    assign data_pair.high = packed_in[15:8];
    assign data_pair.low = byte_val;
    assign byte_out = data_pair.high;
    assign packed_out[15:8] = data_pair.high;
    assign packed_out[7:0] = data_pair.low + byte_val;
endmodule

module deep_comb_assign_chain (
    input wire [15:0] dcac_start_val,
    output logic [15:0] dcac_end_val
);
    logic [15:0] t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    logic [15:0] t11, t12, t13, t14, t15, t16, t17, t18, t19, t20;
    logic [15:0] t21, t22, t23, t24, t25, t26, t27, t28, t29, t30;
    logic [15:0] t31, t32, t33, t34, t35, t36, t37, t38, t39, t40;
    always_comb begin
        t1 = dcac_start_val + 1;
        t2 = t1 * 2;
        t3 = t2 - 3;
        t4 = t3 ^ 4;
        t5 = t4 | 5;
        t6 = t5 & 6;
        t7 = t6 + 7;
        t8 = t7 - 8;
        t9 = t8 ^ 9;
        t10 = t9 | 10;
        t11 = t10 & 11;
        t12 = t11 + 12;
        t13 = t12 - 13;
        t14 = t13 ^ 14;
        t15 = t14 | 15;
        t16 = t15 + 16;
        t17 = t16 * 17;
        t18 = t17 - 18;
        t19 = t18 ^ 19;
        t20 = t19 | 20;
        t21 = t20 + 1;
        t22 = t21 * 2;
        t23 = t22 - 3;
        t24 = t23 ^ 4;
        t25 = t24 | 5;
        t26 = t25 & 6;
        t27 = t26 + 7;
        t28 = t27 - 8;
        t29 = t28 ^ 9;
        t30 = t29 | 10;
        t31 = t30 & 11;
        t32 = t31 + 12;
        t33 = t32 - 13;
        t34 = t33 ^ 14;
        t35 = t34 | 15;
        t36 = t35 + 16;
        t37 = t36 * 17;
        t38 = t37 - 18;
        t39 = t38 ^ 19;
        t40 = t39 | 20;
        dcac_end_val = t40;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_a_1755007877806_507,
    input logic inj_b_1755007877806_233,
    input logic [3:0] inj_data_in_n_1755007877815_345,
    input wire [15:0] inj_dcac_start_val_1755007877808_606,
    input logic [15:0] inj_in_data_1755007877809_192,
    input bit inj_in_h_1755007877812_57,
    input logic [38:0] inj_in_packed_for_conv_1755007877807_241,
    input logic [7:0] inj_in_vec_1755007877807_255,
    input wire reset,
    output logic [7:0] inj_byte_out_1755007877810_557,
    output logic [3:0] inj_data_out1_n_1755007877815_943,
    output logic [3:0] inj_data_out2_n_1755007877815_192,
    output logic [15:0] inj_dcac_end_val_1755007877808_294,
    output int inj_driven_var_1755007877811_799,
    output wire inj_o_c_1755007877806_153,
    output logic inj_out_bit_conv_1755007877807_38,
    output logic [7:0] inj_out_field_a_1755007877809_406,
    output logic [7:0] inj_out_field_b_1755007877809_526,
    output logic inj_out_h_1755007877812_960,
    output logic inj_out_i_1755007877814_291,
    output int inj_out_int_conv_1755007877807_209,
    output logic [7:0] inj_out_unpacked_struct_repacked_1755007877807_173,
    output logic [5:0] inj_out_vec_conv_1755007877807_942,
    output logic [15:0] inj_packed_out_1755007877810_313,
    output logic inj_sum_1755007877806_366
);
    // BEGIN: simple_adder_ts1755007877806
    // BEGIN: module_simple_ts1755007877806
    wire internal_xor_res_ts1755007877806;
        // BEGIN: assign_pattern_lvalue_ts1755007877807
        eight_bit_unpacked_struct_t unpacked_s;
        logic [7:0] reg_unpacked_struct_repacked_ts1755007877807;
        int int_var_ts1755007877807;
        logic bit_var_ts1755007877807;
        logic [5:0] vec_var_ts1755007877807;
            // BEGIN: m_driver_check_ts1755007877811
            int my_driven_var_ts1755007877811;
                // BEGIN: split_multiple_blocking_ts1755007877815
                logic [3:0] temp_n_ts1755007877815;
                always @(*) begin
                    temp_n_ts1755007877815 = inj_data_in_n_1755007877815_345 + 1;
                    inj_data_out1_n_1755007877815_943 = temp_n_ts1755007877815 * 2;
                    inj_data_out2_n_1755007877815_192 = temp_n_ts1755007877815 + 3;
                end
                // END: split_multiple_blocking_ts1755007877815

                LintAsyncFovIssue LintAsyncFovIssue_inst_1755007877814_4153 (
                    .out_i(inj_out_i_1755007877814_291),
                    .clk(clk),
                    .in_h(bit_var_ts1755007877807),
                    .rst_n(reset)
                );
                CoverageHelper CoverageHelper_inst_1755007877812_1460 (
                    .in_h(inj_in_h_1755007877812_57),
                    .out_h(inj_out_h_1755007877812_960)
                );
            function automatic void write_to_var(input int val);
                my_driven_var_ts1755007877811 = val;
            endfunction
            always @(posedge clk) begin
                write_to_var(int_var_ts1755007877807);
            end
            assign inj_driven_var_1755007877811_799 = my_driven_var_ts1755007877811;
            // END: m_driver_check_ts1755007877811

            PackedStructOps PackedStructOps_inst_1755007877810_1024 (
                .byte_out(inj_byte_out_1755007877810_557),
                .packed_out(inj_packed_out_1755007877810_313),
                .byte_val(inj_in_vec_1755007877807_255),
                .packed_in(inj_in_data_1755007877809_192)
            );
            // BEGIN: StructExample_ts1755007877809
            typedef struct packed {
                logic [7:0] field_a_ts1755007877809;
                logic [7:0] field_b_ts1755007877809;
            } example_struct_t;
            example_struct_t my_struct;
            always_comb begin
                my_struct     = inj_in_data_1755007877809_192;
                inj_out_field_a_1755007877809_406   = my_struct.field_a_ts1755007877809;
                inj_out_field_b_1755007877809_526   = my_struct.field_b_ts1755007877809;
            end
            // END: StructExample_ts1755007877809

            deep_comb_assign_chain deep_comb_assign_chain_inst_1755007877808_6032 (
                .dcac_start_val(inj_dcac_start_val_1755007877808_606),
                .dcac_end_val(inj_dcac_end_val_1755007877808_294)
            );
        always_comb begin
            unpacked_s.f1 = inj_in_vec_1755007877807_255[3:0];
            unpacked_s.f2 = inj_in_vec_1755007877807_255[4];
            unpacked_s.f3 = inj_in_vec_1755007877807_255[7:5];
            reg_unpacked_struct_repacked_ts1755007877807 = { unpacked_s.f3, unpacked_s.f2, unpacked_s.f1 };
            int_var_ts1755007877807 = inj_in_packed_for_conv_1755007877807_241[31:0];
            bit_var_ts1755007877807 = inj_in_packed_for_conv_1755007877807_241[32];
            vec_var_ts1755007877807 = inj_in_packed_for_conv_1755007877807_241[38:33];
            inj_out_unpacked_struct_repacked_1755007877807_173 = reg_unpacked_struct_repacked_ts1755007877807;
            inj_out_int_conv_1755007877807_209 = int_var_ts1755007877807;
            inj_out_bit_conv_1755007877807_38 = bit_var_ts1755007877807;
            inj_out_vec_conv_1755007877807_942 = vec_var_ts1755007877807;
        end
        // END: assign_pattern_lvalue_ts1755007877807

    assign internal_xor_res_ts1755007877806 = clk ^ reset;
    assign inj_o_c_1755007877806_153 = internal_xor_res_ts1755007877806 & clk;
    // END: module_simple_ts1755007877806

    assign inj_sum_1755007877806_366 = inj_a_1755007877806_507 + inj_b_1755007877806_233;
    // END: simple_adder_ts1755007877806
endmodule

