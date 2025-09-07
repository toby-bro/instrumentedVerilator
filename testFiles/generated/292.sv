module ModWideBus (
    input logic [31:0] data_in_w,
    output logic [31:0] data_out_w
);
    assign data_out_w = ~data_in_w;
endmodule

module Module_GatePrimitives (
    input wire g_ctrl_n,
    input wire g_ctrl_p,
    input wire g_in,
    output wire g_out_and,
    output wire g_out_or
);
    and a1 (g_out_and, g_in, g_in);
    or  o1 (g_out_or , g_in, g_in);
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
    input logic [7:0] inj_d0_w_1755007852877_637,
    input logic [7:0] inj_d1_w_1755007852877_577,
    input logic [7:0] inj_d2_w_1755007852877_268,
    input logic [7:0] inj_d3_w_1755007852877_196,
    input logic [31:0] inj_data_in_w_1755007852875_468,
    input wire [15:0] inj_dcac_start_val_1755007852874_475,
    input wire inj_g_ctrl_n_1755007852874_242,
    input logic inj_in_a_1755007852875_321,
    input logic [1:0] inj_in_val_1755007852876_961,
    input logic [15:0] inj_in_vec_1755007852878_499,
    input wire reset,
    output logic [31:0] inj_data_out_w_1755007852875_432,
    output logic [15:0] inj_dcac_end_val_1755007852874_216,
    output wire inj_g_out_and_1755007852874_61,
    output wire inj_g_out_or_1755007852874_501,
    output logic inj_out_b_1755007852875_915,
    output logic inj_out_data_pull0_1755007852875_257,
    output logic inj_out_data_pull1_1755007852875_667,
    output logic inj_out_its_1755007852876_48,
    output reg inj_out_res_1755007852876_334,
    output logic [7:0] inj_out_slice_be_1755007852878_43,
    output logic [7:0] inj_out_slice_le_1755007852878_883,
    output logic [7:0] inj_out_w_1755007852877_248
);
    // BEGIN: LintUnusedSignal_ts1755007852875
    logic unused_w_ts1755007852875; 
        // BEGIN: range_select_simple_packed_ts1755007852878
        assign inj_out_slice_be_1755007852878_43 = inj_in_vec_1755007852878_499[7:0]; 
        assign inj_out_slice_le_1755007852878_883 = inj_in_vec_1755007852878_499[7:0]; 
        // END: range_select_simple_packed_ts1755007852878

        // BEGIN: split_case_ts1755007852877
        always @(posedge clk) begin
            case (inj_in_val_1755007852876_961)
                2'b00: inj_out_w_1755007852877_248 <= inj_d0_w_1755007852877_637;
                2'b01: inj_out_w_1755007852877_248 <= inj_d1_w_1755007852877_577;
                2'b10: inj_out_w_1755007852877_248 <= inj_d2_w_1755007852877_268;
                default: inj_out_w_1755007852877_248 <= inj_d3_w_1755007852877_196;
            endcase
        end
        // END: split_case_ts1755007852877

        // BEGIN: case_basic_ts1755007852876
        always_comb begin
            inj_out_res_1755007852876_334 = 1'b0;
            case (inj_in_val_1755007852876_961)
                2'b00: inj_out_res_1755007852876_334 = 1'b0;
                2'b01: inj_out_res_1755007852876_334 = 1'b1;
                2'b10: inj_out_res_1755007852876_334 = 1'b0;
                2'b11: inj_out_res_1755007852876_334 = 1'b1;
            endcase
        end
        // END: case_basic_ts1755007852876

        // BEGIN: ImplicitTimeScaleModule_ts1755007852876
        assign inj_out_its_1755007852876_48 = inj_in_a_1755007852875_321;
        // END: ImplicitTimeScaleModule_ts1755007852876

        ModWideBus ModWideBus_inst_1755007852875_1124 (
            .data_in_w(inj_data_in_w_1755007852875_468),
            .data_out_w(inj_data_out_w_1755007852875_432)
        );
        // BEGIN: module_with_unconnected_drive_ts1755007852875
        assign inj_out_data_pull1_1755007852875_667 = unused_w_ts1755007852875;
        assign inj_out_data_pull0_1755007852875_257 = ~unused_w_ts1755007852875;
        // END: module_with_unconnected_drive_ts1755007852875

    assign inj_out_b_1755007852875_915 = inj_in_a_1755007852875_321;
    // END: LintUnusedSignal_ts1755007852875

    deep_comb_assign_chain deep_comb_assign_chain_inst_1755007852874_7433 (
        .dcac_start_val(inj_dcac_start_val_1755007852874_475),
        .dcac_end_val(inj_dcac_end_val_1755007852874_216)
    );
    Module_GatePrimitives Module_GatePrimitives_inst_1755007852874_9264 (
        .g_ctrl_p(clk),
        .g_in(reset),
        .g_out_and(inj_g_out_and_1755007852874_61),
        .g_out_or(inj_g_out_or_1755007852874_501),
        .g_ctrl_n(inj_g_ctrl_n_1755007852874_242)
    );
endmodule

