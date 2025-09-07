module LintLatch (
    input logic in_j,
    input logic in_k,
    output logic out_l
);
    always_comb begin
        if (in_j) begin
            out_l = in_k;
        end else begin
            out_l = 1'b0; 
        end
    end
endmodule

module SimpleAssign (
    input logic [9:0] val_in,
    output logic [9:0] val_out
);
    assign val_out = val_in;
endmodule

module simple_for_loop (
    input logic [7:0] in_data,
    output logic [7:0] out_sum
);
    logic [7:0] sum;
    always_comb begin
        sum = 8'h00;
        for (int i = 0; i < 5; i = i + 1) begin
            sum = sum + in_data;
        end
        out_sum = sum;
    end
endmodule

module split_combo_blocking (
    input logic [7:0] a_aa,
    input logic [7:0] b_aa,
    input logic [7:0] c_aa,
    output logic [7:0] x_aa,
    output logic [7:0] y_aa,
    output logic [7:0] z_aa
);
    always @(*) begin
        x_aa = a_aa + b_aa;
        y_aa = x_aa - c_aa;
        z_aa = a_aa * c_aa;
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_a_aa_1755007805654_47,
    input logic [7:0] inj_b_aa_1755007805654_515,
    input bit [7:0] inj_data_in_1755007805655_771,
    input logic [31:0] inj_data_in_w_1755007805656_747,
    input logic [7:0] inj_in_data_1755007805654_654,
    input logic inj_in_j_1755007805653_760,
    input logic inj_in_k_1755007805653_33,
    input int inj_index_in_1755007805657_637,
    input bit inj_select_signal_1755007805655_530,
    input logic [4:0] inj_start_bit_1755007805657_843,
    input logic [9:0] inj_val_in_1755007805656_9,
    input wire reset,
    output logic inj_bit_out_1755007805657_706,
    output logic [7:0] inj_byte_out_1755007805657_699,
    output bit [7:0] inj_data_out_1755007805655_68,
    output logic [31:0] inj_data_out_w_1755007805656_593,
    output wire inj_o_c_1755007805653_63,
    output logic inj_out_its_1755007805659_433,
    output logic inj_out_l_1755007805653_255,
    output logic [7:0] inj_out_sum_1755007805654_997,
    output int inj_out_val_1755007805660_388,
    output logic inj_q_1755007805654_302,
    output logic [9:0] inj_val_out_1755007805656_356,
    output logic [7:0] inj_x_aa_1755007805654_262,
    output logic [7:0] inj_y_aa_1755007805654_51,
    output logic [7:0] inj_z_aa_1755007805654_412
);
    // BEGIN: module_simple_ts1755007805653
    wire internal_xor_res_ts1755007805653;
        // BEGIN: SimpleLogicTest_ts1755007805655
        logic [7:0] temp_data_ts1755007805655;
            // BEGIN: invalid_this_diag_mod_ts1755007805660
            assign inj_out_val_1755007805660_388 = inj_index_in_1755007805657_637;
            // END: invalid_this_diag_mod_ts1755007805660

            // BEGIN: ImplicitTimeScaleModule_ts1755007805659
            assign inj_out_its_1755007805659_433 = inj_in_j_1755007805653_760;
            // END: ImplicitTimeScaleModule_ts1755007805659

            // BEGIN: ArrayIndexAndPartSelect_ts1755007805658
            logic [31:0] internal_data = inj_data_in_w_1755007805656_747;
            assign inj_bit_out_1755007805657_706 = internal_data[inj_index_in_1755007805657_637];
            assign inj_byte_out_1755007805657_699 = internal_data[inj_start_bit_1755007805657_843 +: 8];
            // END: ArrayIndexAndPartSelect_ts1755007805658

            // BEGIN: ModWideBus_ts1755007805657
            assign inj_data_out_w_1755007805656_593 = ~inj_data_in_w_1755007805656_747;
            // END: ModWideBus_ts1755007805657

            SimpleAssign SimpleAssign_inst_1755007805656_576 (
                .val_in(inj_val_in_1755007805656_9),
                .val_out(inj_val_out_1755007805656_356)
            );
        always_comb begin
            if (inj_select_signal_1755007805655_530) begin
                temp_data_ts1755007805655 = inj_data_in_1755007805655_771 + 1;
            end else begin
                temp_data_ts1755007805655 = inj_data_in_1755007805655_771 - 1;
            end
            inj_data_out_1755007805655_68 = temp_data_ts1755007805655;
        end
        // END: SimpleLogicTest_ts1755007805655

        split_combo_blocking split_combo_blocking_inst_1755007805654_356 (
            .b_aa(inj_b_aa_1755007805654_515),
            .c_aa(inj_in_data_1755007805654_654),
            .x_aa(inj_x_aa_1755007805654_262),
            .y_aa(inj_y_aa_1755007805654_51),
            .z_aa(inj_z_aa_1755007805654_412),
            .a_aa(inj_a_aa_1755007805654_47)
        );
        // BEGIN: basic_d_flipflop_ts1755007805654
        always_ff @(posedge clk) begin
            inj_q_1755007805654_302 <= inj_in_k_1755007805653_33;
        end
        // END: basic_d_flipflop_ts1755007805654

        simple_for_loop simple_for_loop_inst_1755007805654_992 (
            .in_data(inj_in_data_1755007805654_654),
            .out_sum(inj_out_sum_1755007805654_997)
        );
        LintLatch LintLatch_inst_1755007805653_1579 (
            .in_k(inj_in_k_1755007805653_33),
            .out_l(inj_out_l_1755007805653_255),
            .in_j(inj_in_j_1755007805653_760)
        );
    assign internal_xor_res_ts1755007805653 = clk ^ reset;
    assign inj_o_c_1755007805653_63 = internal_xor_res_ts1755007805653 & clk;
    // END: module_simple_ts1755007805653
endmodule

