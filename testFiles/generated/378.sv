module invalid_this_diag_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module multiplexer_2to1 (
    input logic data0,
    input logic data1,
    input logic sel,
    output logic result
);
    assign result = sel ? data1 : data0;
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
    input logic inj_data0_1755007881077_549,
    input logic inj_data1_1755007881077_792,
    input wire [3:0] inj_data_c_1755007881079_513,
    input wire [7:0] inj_in_array_data_1755007881077_568,
    input int inj_in_val_1755007881077_133,
    input logic [7:0] inj_input_bf_1755007881078_441,
    input logic [3:0] inj_input_bf_slice_1755007881078_671,
    input wire [1:0] inj_select_idx_1755007881077_118,
    input logic inj_tok_in_1755007881077_828,
    input logic [7:0] inj_v2_x_1755007881078_12,
    input logic [7:0] inj_v3_x_1755007881078_32,
    input logic [9:0] inj_val_in_1755007881077_351,
    input wire reset,
    output logic inj_out1_1755007881079_97,
    output logic [3:0] inj_out_case_case_1755007881079_967,
    output logic [3:0] inj_out_case_casex_1755007881079_179,
    output logic [3:0] inj_out_case_casez_1755007881079_254,
    output wire [3:0] inj_out_element_1755007881077_639,
    output int inj_out_val_1755007881077_296,
    output logic [7:0] inj_out_x_1755007881078_815,
    output logic [7:0] inj_output_bf_1755007881078_369,
    output logic [3:0] inj_output_bf_slice_1755007881078_199,
    output logic inj_result_1755007881077_256,
    output logic inj_tok_out_1755007881077_351,
    output logic [9:0] inj_val_out_1755007881077_519
);
    // BEGIN: Module_MacroTokens_ts1755007881077
    // BEGIN: SimpleAssign_ts1755007881077
    // BEGIN: module_bitfield_concat_ts1755007881078
    logic [7:0] my_bitfield_ts1755007881078 ;
        // BEGIN: ModuleLineDirective_ts1755007881079
        logic internal_sig_a_ts1755007881079;
        logic internal_sig_b_ts1755007881079;
        logic unused_line_var_ts1755007881079;
            // BEGIN: CaseStatementConditions_ts1755007881080
            always_comb begin
                case (inj_select_idx_1755007881077_118)
                    2'b00: inj_out_case_case_1755007881079_967 = inj_data_c_1755007881079_513;
                    2'b01: inj_out_case_case_1755007881079_967 = inj_data_c_1755007881079_513 + 1;
                    2'b10: inj_out_case_case_1755007881079_967 = inj_data_c_1755007881079_513 + 2;
                    default: inj_out_case_case_1755007881079_967 = 4'bxxxx;
                endcase
                casez (inj_select_idx_1755007881077_118)
                    2'b0?: inj_out_case_casez_1755007881079_254 = inj_data_c_1755007881079_513 + 10;
                    2'b1?: inj_out_case_casez_1755007881079_254 = inj_data_c_1755007881079_513 + 20;
                    default: inj_out_case_casez_1755007881079_254 = 4'bzzzz;
                endcase
                casex (inj_select_idx_1755007881077_118)
                    2'b0?: inj_out_case_casex_1755007881079_179 = inj_data_c_1755007881079_513 - 1;
                    2'b1?: inj_out_case_casex_1755007881079_179 = inj_data_c_1755007881079_513 - 2;
                    default: inj_out_case_casex_1755007881079_179 = 4'bxxxx;
                endcase
            end
            // END: CaseStatementConditions_ts1755007881080

        `line 100 "virtual_file_A.sv" 1
        assign internal_sig_a_ts1755007881079 = inj_tok_in_1755007881077_828;
        `line 20 "virtual_file_B.sv" 1
        assign internal_sig_b_ts1755007881079 = ~internal_sig_a_ts1755007881079;
        assign unused_line_var_ts1755007881079 = 1'b1;
        `line 150 "virtual_file_A.sv" 2
        assign inj_out1_1755007881079_97 = internal_sig_b_ts1755007881079;
        `line 1 "original_file.sv" 0
        // END: ModuleLineDirective_ts1755007881079

        // BEGIN: split_ifelse_chain_ts1755007881078
        always @(posedge clk) begin
            if (inj_tok_in_1755007881077_828) begin
                inj_out_x_1755007881078_815 <= my_bitfield_ts1755007881078;
            end else if (inj_data0_1755007881077_549) begin
                inj_out_x_1755007881078_815 <= inj_v2_x_1755007881078_12;
            end else if (inj_data1_1755007881077_792) begin
                inj_out_x_1755007881078_815 <= inj_v3_x_1755007881078_32;
            end else begin
                inj_out_x_1755007881078_815 <= inj_input_bf_1755007881078_441;
            end
        end
        // END: split_ifelse_chain_ts1755007881078

    always_comb begin
        if (inj_input_bf_1755007881078_441[7]) begin
            my_bitfield_ts1755007881078 = inj_input_bf_1755007881078_441;
        end else begin
            my_bitfield_ts1755007881078 = {inj_input_bf_1755007881078_441[0], inj_input_bf_1755007881078_441[7:1]};
        end
        my_bitfield_ts1755007881078[3:0] = inj_input_bf_slice_1755007881078_671;
    end
    assign inj_output_bf_1755007881078_369 = my_bitfield_ts1755007881078;
    assign inj_output_bf_slice_1755007881078_199 = my_bitfield_ts1755007881078[3:0];
    // END: module_bitfield_concat_ts1755007881078

    invalid_this_diag_mod invalid_this_diag_mod_inst_1755007881077_8379 (
        .out_val(inj_out_val_1755007881077_296),
        .in_val(inj_in_val_1755007881077_133)
    );
    multiplexer_2to1 multiplexer_2to1_inst_1755007881077_9974 (
        .sel(inj_tok_in_1755007881077_828),
        .result(inj_result_1755007881077_256),
        .data0(inj_data0_1755007881077_549),
        .data1(inj_data1_1755007881077_792)
    );
    assign inj_val_out_1755007881077_519 = inj_val_in_1755007881077_351;
    // END: SimpleAssign_ts1755007881077

    unpacked_array_module unpacked_array_module_inst_1755007881077_9952 (
        .in_array_data(inj_in_array_data_1755007881077_568),
        .select_idx(inj_select_idx_1755007881077_118),
        .out_element(inj_out_element_1755007881077_639)
    );
    `define PASTE(a,b) a``b
    logic `PASTE(my,_var);
    always_comb begin
        `PASTE(my,_var) = inj_tok_in_1755007881077_828;
        inj_tok_out_1755007881077_351         = `PASTE(my,_var);
    end
    // END: Module_MacroTokens_ts1755007881077
endmodule

