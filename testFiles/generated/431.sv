module Comb_Assign (
    input wire in1,
    input wire in2,
    output wire out
);
    assign out = in1 & in2;
endmodule

module IfElseIfChain (
    input logic [7:0] data0,
    input logic [7:0] data1,
    input logic [7:0] data2,
    input logic [7:0] data3,
    input logic [1:0] sel_code,
    output logic [7:0] selected_data
);
    always_comb begin
        if (sel_code == 2'b00) begin
            selected_data = data0;
        end else if (sel_code == 2'b01) begin
            selected_data = data1;
        end else if (sel_code == 2'b10) begin
            selected_data = data2;
        end else begin
            selected_data = data3;
        end
    end
endmodule

module dup_cond (
    input logic [3:0] control,
    input logic [7:0] data_a,
    input logic [7:0] data_b,
    output logic [7:0] result1,
    output logic [7:0] result2
);
    always_comb begin
        result1 = '0;
        result2 = '0;
        if (control[0]) begin
            result1 = data_a + data_b;
        end else begin
            result1 = data_a - data_b;
        end
        if (control[1]) begin
            result2 = data_a - data_b;
        end else begin
            result2 = data_a + data_b;
        end
        case (control[3:2])
            2'b00: result1 = data_a & data_b;
            2'b01: result1 = data_a | data_b;
            2'b10: result2 = data_a & data_b;
            2'b11: result2 = data_a | data_b;
            default: begin result1 = '0; result2 = '0; end
        endcase
        if (control[0] == control[1]) begin
            result1 = result1 + 1;
        end else if (control[2] != control[3]) begin
            result2 = result2 - 1;
        end
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

module snippet #(
    parameter integer DATA_WIDTH = 8
) (
    input wire clk,
    input logic [7:0] inj_a_1755007898361_736,
    input logic [7:0] inj_b_1755007898361_574,
    input logic [7:0] inj_c_1755007898361_28,
    input logic [3:0] inj_control_1755007898370_584,
    input logic [7:0] inj_data0_1755007898362_171,
    input wire [31:0] inj_data_in_1755007898361_699,
    input logic inj_data_value_1755007898364_65,
    input bit inj_enable_crypto_1755007898369_485,
    input wire [7:0] inj_in_array_data_1755007898361_978,
    input logic inj_level1_en_1755007898364_172,
    input logic inj_level2_en_1755007898364_756,
    input logic [1:0] inj_sel_code_1755007898362_688,
    input wire [1:0] inj_select_idx_1755007898361_784,
    input wire reset,
    output bit inj_cfg_out_1755007898373_445,
    output bit inj_crypto_active_1755007898369_500,
    output logic [31:0] inj_data_out_1755007898361_318,
    output logic inj_data_out_1755007898366_237,
    output logic [7:0] inj_out1_1755007898365_949,
    output wire inj_out_1755007898371_682,
    output wire [3:0] inj_out_element_1755007898361_98,
    output wire [7:0] inj_param_out_1755007898362_153,
    output logic [7:0] inj_result1_1755007898370_135,
    output logic [7:0] inj_result2_1755007898370_446,
    output logic [7:0] inj_result_and_1755007898361_302,
    output logic [7:0] inj_result_or_1755007898361_840,
    output logic inj_result_out_1755007898364_976,
    output logic [7:0] inj_result_xor_1755007898361_212,
    output logic [7:0] inj_selected_data_1755007898362_719,
    output bit inj_system_status_clear_1755007898367_712
);
    // BEGIN: BitwiseOperations_ts1755007898361
    // BEGIN: mod_part_select_ts1755007898361
    logic [31:0] temp_reg_ts1755007898361;
        // BEGIN: basic_comb_ts1755007898365
        ;
        logic [7:0] temp_wire_ts1755007898365;
            // BEGIN: Module_ConfigKeywords_ts1755007898373
            assign inj_cfg_out_1755007898373_445 = inj_enable_crypto_1755007898369_485;
            // END: Module_ConfigKeywords_ts1755007898373

            Comb_Assign Comb_Assign_inst_1755007898371_3700 (
                .in2(clk),
                .out(inj_out_1755007898371_682),
                .in1(reset)
            );
            dup_cond dup_cond_inst_1755007898370_4967 (
                .result2(inj_result2_1755007898370_446),
                .control(inj_control_1755007898370_584),
                .data_a(temp_wire_ts1755007898365),
                .data_b(inj_b_1755007898361_574),
                .result1(inj_result1_1755007898370_135)
            );
            // BEGIN: PragmaProtectKeyBlock_ts1755007898369
        `ifdef SLANG_PRAGMA
        `protect key
        `endif
        `ifdef SLANG_PRAGMA
        `protect block
        `endif
        assign inj_crypto_active_1755007898369_500 = inj_enable_crypto_1755007898369_485;
            // END: PragmaProtectKeyBlock_ts1755007898369

            // BEGIN: PragmaResetDirectives_ts1755007898367
        `ifdef SLANG_PRAGMA
        `reset protect diagnostic
        `endif
        assign inj_system_status_clear_1755007898367_712 = reset;
            // END: PragmaResetDirectives_ts1755007898367

            // BEGIN: sequential_register_ts1755007898366
            always_ff @(posedge clk or negedge reset) begin
                if (!reset) begin
                    inj_data_out_1755007898366_237 <= 1'b0; 
                end else if (inj_data_value_1755007898364_65) begin
                    inj_data_out_1755007898366_237 <= inj_level2_en_1755007898364_756; 
                end
            end
            // END: sequential_register_ts1755007898366

        assign temp_wire_ts1755007898365 = inj_data0_1755007898362_171 + inj_b_1755007898361_574;
        always_comb begin
            inj_out1_1755007898365_949 = temp_wire_ts1755007898365;
        end
        // END: basic_comb_ts1755007898365

        // BEGIN: nested_blocks_ts1755007898364
        always_comb begin : main_block 
            inj_result_out_1755007898364_976 = 1'b0; 
            if (inj_level1_en_1755007898364_172) begin : inner_block1 
                if (inj_level2_en_1755007898364_756) begin : inner_block2 
                    inj_result_out_1755007898364_976 = inj_data_value_1755007898364_65;
                end 
            end 
        end
        // END: nested_blocks_ts1755007898364

        IfElseIfChain IfElseIfChain_inst_1755007898362_3895 (
            .selected_data(inj_selected_data_1755007898362_719),
            .data0(inj_data0_1755007898362_171),
            .data1(inj_a_1755007898361_736),
            .data2(inj_b_1755007898361_574),
            .data3(inj_c_1755007898361_28),
            .sel_code(inj_sel_code_1755007898362_688)
        );
        // BEGIN: module_with_params_ts1755007898362
        assign inj_param_out_1755007898362_153 = inj_in_array_data_1755007898361_978;
        // END: module_with_params_ts1755007898362

    always_comb begin
        temp_reg_ts1755007898361[7:0] = inj_data_in_1755007898361_699[7:0];
        temp_reg_ts1755007898361[15:8] = inj_data_in_1755007898361_699[23:16];
        temp_reg_ts1755007898361[31:16] = inj_data_in_1755007898361_699[15:0];
        temp_reg_ts1755007898361[0] = inj_data_in_1755007898361_699[31];
        temp_reg_ts1755007898361[8] = inj_data_in_1755007898361_699[0];
        inj_data_out_1755007898361_318 = temp_reg_ts1755007898361;
    end
    // END: mod_part_select_ts1755007898361

    assign inj_result_and_1755007898361_302 = inj_a_1755007898361_736 & inj_b_1755007898361_574;
    assign inj_result_or_1755007898361_840 = inj_a_1755007898361_736 | inj_c_1755007898361_28;
    assign inj_result_xor_1755007898361_212 = inj_b_1755007898361_574 ^ inj_c_1755007898361_28;
    // END: BitwiseOperations_ts1755007898361

    unpacked_array_module unpacked_array_module_inst_1755007898361_9192 (
        .out_element(inj_out_element_1755007898361_98),
        .in_array_data(inj_in_array_data_1755007898361_978),
        .select_idx(inj_select_idx_1755007898361_784)
    );
endmodule

