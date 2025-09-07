interface struct_if;
    logic [7:0] packet_field1;
    logic [7:0] packet_field2;
    logic tx_en;
    modport Access (output packet_field1, output packet_field2, output tx_en);
endinterface
module ArrayIndexAndPartSelect (
    input logic [31:0] data_in,
    input int index_in,
    input logic [4:0] start_bit,
    output logic bit_out,
    output logic [7:0] byte_out
);
    logic [31:0] internal_data = data_in;
    assign bit_out = internal_data[index_in];
    assign byte_out = internal_data[start_bit +: 8];
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

module snippet (
    input wire clk,
    input logic [3:0] inj_a_1755004214225_273,
    input logic [3:0] inj_b_1755004214225_373,
    input logic [31:0] inj_data_in_1755004214225_614,
    input logic [7:0] inj_in2_1755004214227_523,
    input logic [7:0] inj_in_data_1755004214225_440,
    input logic [7:0] inj_in_field2_1755004214225_150,
    input int inj_index_in_1755004214225_610,
    input logic [4:0] inj_start_bit_1755004214225_428,
    input wire reset,
    output logic inj_bit_out_1755004214225_225,
    output logic [7:0] inj_byte_out_1755004214225_363,
    output logic [7:0] inj_data_out_1755004214229_8,
    output logic inj_dout_a_1755004214231_98,
    output logic inj_dout_b_1755004214231_264,
    output wire inj_o_1755004214228_80,
    output logic inj_o_out_1755004214226_691,
    output logic inj_o_reg_out_1755004214230_74,
    output logic [7:0] inj_o_target_result_1755004214227_48,
    output logic [7:0] inj_o_target_result_1755004214227_496,
    output wire inj_o_wire_out_1755004214230_776,
    output logic inj_out1_1755004214228_961,
    output logic [7:0] inj_out_1755004214227_448,
    output logic inj_out_1755004214230_291,
    output logic [7:0] inj_out_reg_d_1755004214233_956,
    output logic [7:0] inj_out_sum_1755004214225_228,
    output logic [7:0] inj_out_v_1755004214232_691,
    output int inj_out_val_1755004214226_205,
    output int inj_out_val_1755004214226_545,
    output logic inj_reset_1755004214225_458,
    output logic [3:0] inj_sum_1755004214225_294,
    output logic inj_tx_status_1755004214225_641
);
    // BEGIN: cu_timeunit_mod_ts1755004214225
    logic internal_sig_ts1755004214225;
        // BEGIN: ModuleLineDirective_ts1755004214228
        logic internal_sig_a_ts1755004214228;
        logic internal_sig_b_ts1755004214228;
        logic unused_line_var_ts1755004214228;
            // BEGIN: nets_alias_clocking_ts1755004214230
            wire  w_internal_ts1755004214230;
            logic r_internal_ts1755004214230;
                // BEGIN: split_conditional_nb_ts1755004214233
                always @(posedge clk) begin
                    if (internal_sig_a_ts1755004214228) begin
                        inj_out_reg_d_1755004214233_956 <= inj_in_field2_1755004214225_150;
                    end else begin
                        inj_out_reg_d_1755004214233_956 <= inj_in2_1755004214227_523;
                    end
                end
                // END: split_conditional_nb_ts1755004214233

                // BEGIN: ModVectorAdd_ts1755004214232
                assign inj_out_v_1755004214232_691 = inj_in2_1755004214227_523 + 8'h01;
                // END: ModVectorAdd_ts1755004214232

                // BEGIN: ModMultipleAlways_ts1755004214231
                always @(posedge clk or negedge reset) begin 
                if (!reset) begin 
                    inj_dout_a_1755004214231_98 <= 1'b0;
                end else begin
                    inj_dout_a_1755004214231_98 <= r_internal_ts1755004214230; 
                end
                end
                always @(posedge clk) begin 
                inj_dout_b_1755004214231_264 <= internal_sig_b_ts1755004214228; 
                end
                // END: ModMultipleAlways_ts1755004214231

            assign w_internal_ts1755004214230  = clk & unused_line_var_ts1755004214228;
            assign inj_o_wire_out_1755004214230_776  = w_internal_ts1755004214230;
            always_ff @(posedge clk) r_internal_ts1755004214230 <= internal_sig_a_ts1755004214228;
            assign inj_o_reg_out_1755004214230_74 = r_internal_ts1755004214230;
            // END: nets_alias_clocking_ts1755004214230

            // BEGIN: simple_xor_gate_ts1755004214230
            assign inj_out_1755004214230_291 = internal_sig_ts1755004214225 ^ internal_sig_a_ts1755004214228;
            // END: simple_xor_gate_ts1755004214230

            // BEGIN: cu_base_ts1755004214229
            assign inj_data_out_1755004214229_8 = inj_in_data_1755004214225_440;
            // END: cu_base_ts1755004214229

        `line 100 "virtual_file_A.sv" 1
        assign internal_sig_a_ts1755004214228 = internal_sig_ts1755004214225;
        `line 20 "virtual_file_B.sv" 1
        assign internal_sig_b_ts1755004214228 = ~internal_sig_a_ts1755004214228;
        assign unused_line_var_ts1755004214228 = 1'b1;
        `line 150 "virtual_file_A.sv" 2
        assign inj_out1_1755004214228_961 = internal_sig_b_ts1755004214228;
        `line 1 "original_file.sv" 0
        // END: ModuleLineDirective_ts1755004214228

        // BEGIN: buf_primitive_ts1755004214228
        buf b1 (inj_o_1755004214228_80, reset);
        // END: buf_primitive_ts1755004214228

        // BEGIN: bitwise_ops_ts1755004214228
        assign inj_out_1755004214227_448 = (inj_in_data_1755004214225_440 & inj_in2_1755004214227_523) | (~inj_in_field2_1755004214225_150) ^ (inj_in_data_1755004214225_440 << 2) >> 1;
        // END: bitwise_ops_ts1755004214228

        // BEGIN: target_module_for_bind_ts1755004214227
        always_comb inj_o_target_result_1755004214227_48 = inj_in_data_1755004214225_440 + 1;
        // END: target_module_for_bind_ts1755004214227

        // BEGIN: target_module_for_bind_ts1755004214227
        always_comb inj_o_target_result_1755004214227_496 = inj_in_data_1755004214225_440 + 1;
        // END: target_module_for_bind_ts1755004214227

        // BEGIN: extern_declarations_ts1755004214226
        assign inj_o_out_1755004214226_691 = internal_sig_ts1755004214225;
        // END: extern_declarations_ts1755004214226

        // BEGIN: unknown_class_pkg_diag_mod_ts1755004214226
        assign inj_out_val_1755004214226_205 = inj_index_in_1755004214225_610;
        // END: unknown_class_pkg_diag_mod_ts1755004214226

        // BEGIN: recursive_param_diag_mod_ts1755004214226
        assign inj_out_val_1755004214226_545 = inj_index_in_1755004214225_610;
        // END: recursive_param_diag_mod_ts1755004214226

        ArrayIndexAndPartSelect ArrayIndexAndPartSelect_inst_1755004214225_5290 (
            .index_in(inj_index_in_1755004214225_610),
            .start_bit(inj_start_bit_1755004214225_428),
            .bit_out(inj_bit_out_1755004214225_225),
            .byte_out(inj_byte_out_1755004214225_363),
            .data_in(inj_data_in_1755004214225_614)
        );
        // BEGIN: module_struct_write_ts1755004214225
        struct_if stif_inst();
        always_comb begin
            stif_inst.packet_field1 = inj_in_data_1755004214225_440;
            stif_inst.packet_field2 = inj_in_field2_1755004214225_150;
            stif_inst.tx_en = 1'b1;
            inj_tx_status_1755004214225_641 = stif_inst.tx_en;
        end
        // END: module_struct_write_ts1755004214225

        // BEGIN: CombinationalLogicImplicit_ts1755004214225
        always @* begin
            inj_sum_1755004214225_294 = inj_a_1755004214225_273 + inj_b_1755004214225_373;
        end
        // END: CombinationalLogicImplicit_ts1755004214225

    always_ff @(posedge clk) begin
        inj_reset_1755004214225_458 <= 1'b0;
        internal_sig_ts1755004214225 = clk;
    end
    // END: cu_timeunit_mod_ts1755004214225

    simple_for_loop simple_for_loop_inst_1755004214225_9250 (
        .in_data(inj_in_data_1755004214225_440),
        .out_sum(inj_out_sum_1755004214225_228)
    );
endmodule

