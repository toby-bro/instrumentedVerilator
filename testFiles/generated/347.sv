module LintSensitiveList (
    input logic in_p,
    input logic in_q,
    output logic out_r
);
    always_comb begin
        out_r = in_p | in_q;
    end
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

module snippet (
    input wire clk,
    input bit inj_cfg_in_1755007870639_886,
    input logic [3:0] inj_data1_1755007870638_946,
    input logic [3:0] inj_data2_1755007870638_563,
    input logic [3:0] inj_data3_1755007870638_616,
    input logic [7:0] inj_denominator_1755007870637_978,
    input logic [15:0] inj_dividend_mod_1755007870637_335,
    input logic [7:0] inj_divisor_mod_1755007870637_760,
    input logic inj_enable_pa_1755007870636_405,
    input logic inj_in_q_1755007870638_995,
    input logic [31:0] inj_input_pa_1755007870636_873,
    input logic [3:0] inj_input_slice_pa_1755007870636_967,
    input logic [15:0] inj_numerator_1755007870637_195,
    input logic [1:0] inj_sel_in_1755007870638_199,
    input wire reset,
    output bit inj_cfg_out_1755007870639_197,
    output logic [3:0] inj_data_out_case_1755007870638_835,
    output logic inj_out_r_1755007870638_52,
    output logic [7:0] inj_out_val_1755007870641_136,
    output logic [7:0] inj_output_pa_1755007870636_140,
    output logic [7:0] inj_output_pa_element1_1755007870636_753,
    output logic [15:0] inj_quotient_1755007870637_728,
    output logic [7:0] inj_remainder_1755007870637_775,
    output logic [7:0] inj_result1_1755007870640_73,
    output logic [7:0] inj_result2_1755007870640_588
);
    // BEGIN: module_packed_array_ts1755007870637
    logic [7:0] my_packed_array[0:3] ;
    // BEGIN: ModuleGenerateIf_ts1755007870642
    parameter int PROCESS_ENABLE = 1;
    logic [7:0] processed_val_ts1755007870642;
    generate
        if (PROCESS_ENABLE) begin : process_block
            assign processed_val_ts1755007870642 = inj_divisor_mod_1755007870637_760 + 10;
        end else begin : bypass_block
            assign processed_val_ts1755007870642 = inj_divisor_mod_1755007870637_760;
        end
    endgenerate
    assign inj_out_val_1755007870641_136 = processed_val_ts1755007870642;
    // END: ModuleGenerateIf_ts1755007870642

    // BEGIN: dup_cond_ts1755007870640
    always_comb begin
        inj_result1_1755007870640_73 = '0;
        inj_result2_1755007870640_588 = '0;
        if (inj_input_slice_pa_1755007870636_967[0]) begin
            inj_result1_1755007870640_73 = inj_denominator_1755007870637_978 + inj_divisor_mod_1755007870637_760;
        end else begin
            inj_result1_1755007870640_73 = inj_denominator_1755007870637_978 - inj_divisor_mod_1755007870637_760;
        end
        if (inj_input_slice_pa_1755007870636_967[1]) begin
            inj_result2_1755007870640_588 = inj_denominator_1755007870637_978 - inj_divisor_mod_1755007870637_760;
        end else begin
            inj_result2_1755007870640_588 = inj_denominator_1755007870637_978 + inj_divisor_mod_1755007870637_760;
        end
        case (inj_input_slice_pa_1755007870636_967[3:2])
            2'b00: inj_result1_1755007870640_73 = inj_denominator_1755007870637_978 & inj_divisor_mod_1755007870637_760;
            2'b01: inj_result1_1755007870640_73 = inj_denominator_1755007870637_978 | inj_divisor_mod_1755007870637_760;
            2'b10: inj_result2_1755007870640_588 = inj_denominator_1755007870637_978 & inj_divisor_mod_1755007870637_760;
            2'b11: inj_result2_1755007870640_588 = inj_denominator_1755007870637_978 | inj_divisor_mod_1755007870637_760;
            default: begin inj_result1_1755007870640_73 = '0; inj_result2_1755007870640_588 = '0; end
        endcase
        if (inj_input_slice_pa_1755007870636_967[0] == inj_input_slice_pa_1755007870636_967[1]) begin
            inj_result1_1755007870640_73 = inj_result1_1755007870640_73 + 1;
        end else if (inj_input_slice_pa_1755007870636_967[2] != inj_input_slice_pa_1755007870636_967[3]) begin
            inj_result2_1755007870640_588 = inj_result2_1755007870640_588 - 1;
        end
    end
    // END: dup_cond_ts1755007870640

    // BEGIN: Module_ConfigKeywords_ts1755007870639
    assign inj_cfg_out_1755007870639_197 = inj_cfg_in_1755007870639_886;
    // END: Module_ConfigKeywords_ts1755007870639

    LintSensitiveList LintSensitiveList_inst_1755007870638_8287 (
        .in_p(inj_enable_pa_1755007870636_405),
        .in_q(inj_in_q_1755007870638_995),
        .out_r(inj_out_r_1755007870638_52)
    );
    // BEGIN: case_selector_ts1755007870638
    always_comb begin
        case (inj_sel_in_1755007870638_199)
            2'b00: inj_data_out_case_1755007870638_835 = inj_input_slice_pa_1755007870636_967; 
            2'b01: inj_data_out_case_1755007870638_835 = inj_data1_1755007870638_946; 
            2'b10: inj_data_out_case_1755007870638_835 = inj_data2_1755007870638_563; 
            default: inj_data_out_case_1755007870638_835 = inj_data3_1755007870638_616; 
        endcase
    end
    // END: case_selector_ts1755007870638

    div_mod_ops div_mod_ops_inst_1755007870637_5780 (
        .quotient(inj_quotient_1755007870637_728),
        .remainder(inj_remainder_1755007870637_775),
        .denominator(inj_denominator_1755007870637_978),
        .dividend_mod(inj_dividend_mod_1755007870637_335),
        .divisor_mod(inj_divisor_mod_1755007870637_760),
        .numerator(inj_numerator_1755007870637_195)
    );
    always_comb begin
        if (inj_enable_pa_1755007870636_405) begin
            my_packed_array[0] = inj_input_pa_1755007870636_873[7:0];
            my_packed_array[1] = inj_input_pa_1755007870636_873[15:8];
            my_packed_array[2] = inj_input_pa_1755007870636_873[23:16];
            my_packed_array[3] = my_packed_array[0] + my_packed_array[1];
        end else begin
            my_packed_array[0] = 8'h0;
            my_packed_array[1] = 8'h0;
            my_packed_array[2] = 8'h0;
            my_packed_array[3] = 8'h0;
        end
        my_packed_array[0][3:0] = inj_input_slice_pa_1755007870636_967;
    end
    assign inj_output_pa_1755007870636_140 = my_packed_array[3];
    assign inj_output_pa_element1_1755007870636_753 = my_packed_array[1];
    // END: module_packed_array_ts1755007870637
endmodule

