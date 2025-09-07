module macro_concat_user (
    input logic [3:0] concat_in,
    output logic [7:0] concat_out
);
    `define MAKE_NAME(a,b) a``b
    logic var_signal;
    always_comb begin
        `MAKE_NAME(var,_signal) = concat_in[0];
    end
    assign concat_out = {4'b0, concat_in[3:1], var_signal};
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_concat_in_1755004205571_45,
    input logic inj_cond_dd_1755004205574_437,
    input logic [7:0] inj_i1_r_1755004205552_287,
    input logic [7:0] inj_i2_r_1755004205552_253,
    input logic [7:0] inj_i3_r_1755004205552_638,
    input wire [7:0] inj_in_a_1755004205553_912,
    input wire [7:0] inj_in_b_1755004205553_493,
    input wire [7:0] inj_in_c_1755004205553_47,
    input wire [7:0] inj_in_const1_1755004205553_756,
    input wire [7:0] inj_in_const2_1755004205553_849,
    input logic [2:0] inj_in_val_1755004205552_479,
    input logic [31:0] inj_in_val_1755004205562_218,
    input int inj_index_in_1755004205566_755,
    input bit inj_select_a_1755004205562_215,
    input wire reset,
    output logic [7:0] inj_concat_out_1755004205571_877,
    output wire inj_data_d_1755004205577_628,
    output logic [7:0] inj_o1_r_1755004205552_969,
    output logic [7:0] inj_o2_r_1755004205552_997,
    output logic [7:0] inj_o3_r_1755004205552_772,
    output logic [7:0] inj_out1_dd_1755004205574_214,
    output logic [7:0] inj_out2_dd_1755004205574_817,
    output logic [7:0] inj_out_add_assoc_1755004205553_351,
    output logic [7:0] inj_out_and_assoc_1755004205553_918,
    output logic [7:0] inj_out_and_swap_const_1755004205553_120,
    output logic [7:0] inj_out_arith_1755004205553_372,
    output logic inj_out_bit_1755004205566_764,
    output logic [7:0] inj_out_bitwise_1755004205553_24,
    output logic inj_out_logical_1755004205553_274,
    output logic [7:0] inj_out_mul_assoc_1755004205553_668,
    output logic [7:0] inj_out_negate_1755004205553_917,
    output logic [7:0] inj_out_or_assoc_1755004205553_611,
    output logic [7:0] inj_out_or_swap_not_1755004205553_51,
    output reg inj_out_res_1755004205552_289,
    output logic [3:0] inj_out_slice_1755004205566_362,
    output logic [7:0] inj_out_unary_not_1755004205553_940,
    output logic [31:0] inj_out_val_1755004205562_388,
    output logic [7:0] inj_out_val_1755004205568_366,
    output logic [7:0] inj_out_xor_assoc_1755004205553_457,
    output logic [7:0] inj_out_xor_swap_var_1755004205553_856,
    output logic [7:0] inj_result_and_1755004205564_569,
    output logic [7:0] inj_result_or_1755004205564_972,
    output logic [7:0] inj_result_xor_1755004205564_209
);
    // BEGIN: split_complex_blocking_ts1755004205552
    logic [7:0] t1_r_ts1755004205552, t2_r_ts1755004205552;
        // BEGIN: Mod_BasicOps_ts1755004205560
        logic [7:0] intermediate_arith_ts1755004205558;
        logic [7:0] intermediate_bitwise_ts1755004205558;
        logic [0:0] intermediate_logical_ts1755004205558;
        logic [7:0] intermediate_add_assoc_ts1755004205558;
        logic [7:0] intermediate_mul_assoc_ts1755004205558;
        logic [7:0] intermediate_and_assoc_ts1755004205558;
        logic [7:0] intermediate_or_assoc_ts1755004205558;
        logic [7:0] intermediate_xor_assoc_ts1755004205558;
            // BEGIN: ModuleGenerateIf_ts1755004205569
            parameter int PROCESS_ENABLE = 1;
            logic [7:0] processed_val_ts1755004205569;
                // BEGIN: simple_logic_b_ts1755004205577
                assign inj_data_d_1755004205577_628 = reset;
                // END: simple_logic_b_ts1755004205577

                // BEGIN: split_multi_nb_in_if_ts1755004205574
                always @(posedge clk) begin
                    if (inj_cond_dd_1755004205574_437) begin
                        inj_out1_dd_1755004205574_214 <= intermediate_xor_assoc_ts1755004205558 + intermediate_bitwise_ts1755004205558;
                        inj_out2_dd_1755004205574_817 <= intermediate_and_assoc_ts1755004205558 - intermediate_add_assoc_ts1755004205558;
                    end else begin
                        inj_out1_dd_1755004205574_214 <= intermediate_xor_assoc_ts1755004205558 * intermediate_bitwise_ts1755004205558;
                        inj_out2_dd_1755004205574_817 <= intermediate_and_assoc_ts1755004205558 / (intermediate_add_assoc_ts1755004205558 + 1);
                    end
                end
                // END: split_multi_nb_in_if_ts1755004205574

                macro_concat_user macro_concat_user_inst_1755004205571_168 (
                    .concat_in(inj_concat_in_1755004205571_45),
                    .concat_out(inj_concat_out_1755004205571_877)
                );
            generate
                if (PROCESS_ENABLE) begin : process_block
                    assign processed_val_ts1755004205569 = intermediate_mul_assoc_ts1755004205558 + 10;
                end else begin : bypass_block
                    assign processed_val_ts1755004205569 = intermediate_mul_assoc_ts1755004205558;
                end
            endgenerate
            assign inj_out_val_1755004205568_366 = processed_val_ts1755004205569;
            // END: ModuleGenerateIf_ts1755004205569

            // BEGIN: element_select_packed_ts1755004205566
            always_comb begin
                if (inj_index_in_1755004205566_755 >= 0 && inj_index_in_1755004205566_755 < 8)
                    inj_out_bit_1755004205566_764 = intermediate_xor_assoc_ts1755004205558[inj_index_in_1755004205566_755];
                else
                    inj_out_bit_1755004205566_764 = 'x; 
            end
            assign inj_out_slice_1755004205566_362 = intermediate_xor_assoc_ts1755004205558[6:3];
            // END: element_select_packed_ts1755004205566

            // BEGIN: BitwiseOperations_ts1755004205564
            assign inj_result_and_1755004205564_569 = intermediate_and_assoc_ts1755004205558 & inj_i2_r_1755004205552_253;
            assign inj_result_or_1755004205564_972 = intermediate_and_assoc_ts1755004205558 | intermediate_xor_assoc_ts1755004205558;
            assign inj_result_xor_1755004205564_209 = inj_i2_r_1755004205552_253 ^ intermediate_xor_assoc_ts1755004205558;
            // END: BitwiseOperations_ts1755004205564

            // BEGIN: member_access_packed_union_ts1755004205562
            typedef union packed {
                logic [31:0] a_ts1755004205562; 
                logic [31:0] b_ts1755004205562; 
            } my_packed_union;
            my_packed_union union_var;
            always_comb begin
                if (inj_select_a_1755004205562_215)
                    union_var.a_ts1755004205562 = inj_in_val_1755004205562_218;
                else
                    union_var.b_ts1755004205562 = inj_in_val_1755004205562_218[31:0];
                inj_out_val_1755004205562_388 = union_var.a_ts1755004205562;
            end
            // END: member_access_packed_union_ts1755004205562

        parameter [7:0] CONST_ZERO = 8'h00;
        always_comb begin
            intermediate_arith_ts1755004205558 = inj_in_a_1755004205553_912;
            intermediate_arith_ts1755004205558 = intermediate_arith_ts1755004205558 + inj_in_b_1755004205553_493;
            intermediate_arith_ts1755004205558 = intermediate_arith_ts1755004205558 - inj_in_c_1755004205553_47;
            intermediate_arith_ts1755004205558 = intermediate_arith_ts1755004205558 * inj_in_const1_1755004205553_756;
            if (inj_in_b_1755004205553_493 != CONST_ZERO) begin
                intermediate_arith_ts1755004205558 = intermediate_arith_ts1755004205558 / inj_in_b_1755004205553_493;
                intermediate_arith_ts1755004205558 = intermediate_arith_ts1755004205558 % inj_in_b_1755004205553_493;
            end else begin
                intermediate_arith_ts1755004205558 = 'x;
            end
            inj_out_arith_1755004205553_372 = intermediate_arith_ts1755004205558;
            intermediate_bitwise_ts1755004205558 = inj_in_a_1755004205553_912;
            intermediate_bitwise_ts1755004205558 = intermediate_bitwise_ts1755004205558 & inj_in_b_1755004205553_493;
            intermediate_bitwise_ts1755004205558 = intermediate_bitwise_ts1755004205558 | inj_in_c_1755004205553_47;
            intermediate_bitwise_ts1755004205558 = intermediate_bitwise_ts1755004205558 ^ inj_in_const1_1755004205553_756;
            inj_out_bitwise_1755004205553_24 = intermediate_bitwise_ts1755004205558;
            intermediate_logical_ts1755004205558 = (inj_in_a_1755004205553_912 != CONST_ZERO) && (inj_in_b_1755004205553_493 != CONST_ZERO);
            intermediate_logical_ts1755004205558 = intermediate_logical_ts1755004205558 || (inj_in_c_1755004205553_47 != CONST_ZERO);
            inj_out_logical_1755004205553_274 = !intermediate_logical_ts1755004205558;
            inj_out_unary_not_1755004205553_940 = ~inj_in_a_1755004205553_912;
            inj_out_negate_1755004205553_917 = -inj_in_a_1755004205553_912;
            intermediate_add_assoc_ts1755004205558 = (inj_in_a_1755004205553_912 + inj_in_b_1755004205553_493) + inj_in_c_1755004205553_47;
            inj_out_add_assoc_1755004205553_351 = intermediate_add_assoc_ts1755004205558;
            intermediate_mul_assoc_ts1755004205558 = (inj_in_a_1755004205553_912 * inj_in_b_1755004205553_493) * inj_in_c_1755004205553_47;
            inj_out_mul_assoc_1755004205553_668 = intermediate_mul_assoc_ts1755004205558;
            intermediate_and_assoc_ts1755004205558 = (inj_in_a_1755004205553_912 & inj_in_b_1755004205553_493) & inj_in_c_1755004205553_47;
            inj_out_and_assoc_1755004205553_918 = intermediate_and_assoc_ts1755004205558;
            intermediate_or_assoc_ts1755004205558 = (inj_in_a_1755004205553_912 | inj_in_b_1755004205553_493) | inj_in_c_1755004205553_47;
            inj_out_or_assoc_1755004205553_611 = intermediate_or_assoc_ts1755004205558;
            intermediate_xor_assoc_ts1755004205558 = (inj_in_a_1755004205553_912 ^ inj_in_b_1755004205553_493) ^ inj_in_c_1755004205553_47;
            inj_out_xor_assoc_1755004205553_457 = intermediate_xor_assoc_ts1755004205558;
            inj_out_and_swap_const_1755004205553_120 = inj_in_const1_1755004205553_756 & inj_in_a_1755004205553_912;
            inj_out_or_swap_not_1755004205553_51 = (~inj_in_a_1755004205553_912) | inj_in_b_1755004205553_493;
            inj_out_xor_swap_var_1755004205553_856 = inj_in_b_1755004205553_493 ^ inj_in_c_1755004205553_47;
        end
        // END: Mod_BasicOps_ts1755004205560

        // BEGIN: casez_xz_ts1755004205553
        always_comb begin
            inj_out_res_1755004205552_289 = 1'b0;
            casez (inj_in_val_1755004205552_479)
                3'b1??: inj_out_res_1755004205552_289 = 1'b1;
                3'b0z?: inj_out_res_1755004205552_289 = 1'b0;
                default: inj_out_res_1755004205552_289 = 1'b1;
            endcase
        end
        // END: casez_xz_ts1755004205553

    always @(*) begin
        t1_r_ts1755004205552 = inj_i1_r_1755004205552_287 + inj_i2_r_1755004205552_253;
        inj_o1_r_1755004205552_969 = t1_r_ts1755004205552 - inj_i3_r_1755004205552_638;
        t2_r_ts1755004205552 = inj_i2_r_1755004205552_253 * inj_i3_r_1755004205552_638;
        inj_o2_r_1755004205552_997 = t1_r_ts1755004205552 + t2_r_ts1755004205552;
        inj_o3_r_1755004205552_772 = t2_r_ts1755004205552 / 2;
    end
    // END: split_complex_blocking_ts1755004205552
endmodule

