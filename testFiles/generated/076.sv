module CombinationalLogicImplicit (
    input logic [3:0] a,
    input logic [3:0] b,
    output logic [3:0] sum
);
    always @* begin
        sum = a + b;
    end
endmodule

module LintParamUnused #(
    parameter integer UNUSED_PARAM = 8
) (
    input logic in_m,
    output logic out_n
);
    assign out_n = in_m;
endmodule

module packed_struct_module (
    input wire [15:0] in_packed_data,
    output wire [7:0] out_byte
);
    typedef struct packed {
        logic [7:0] byte1;
        logic [7:0] byte2;
    } my_packed_struct_t;
    my_packed_struct_t data_struct;
    assign data_struct = in_packed_data;
    assign out_byte = data_struct.byte1;
endmodule

module split_conditional_blocking (
    input logic condition_o,
    input logic [7:0] in_false_o,
    input logic [7:0] in_true_o,
    output logic [7:0] out_val_o
);
    always @(*) begin
        if (condition_o) begin
            out_val_o = in_true_o;
        end else begin
            out_val_o = in_false_o;
        end
    end
endmodule

module typedef_struct_public_mod (
    input logic [15:0] packed_in,
    output logic [7:0] field2_o
);
    typedef struct packed {
        logic [7:0] field1;
        logic [7:0] field2;
    } my_public_packed_struct_t;
    my_public_packed_struct_t my_struct_var;
    always_comb begin
        my_struct_var = packed_in;
    end
    assign field2_o = my_struct_var.field2;
endmodule

module snippet #(
    parameter integer UNUSED_PARAM = 8
) (
    input wire clk,
    input logic [3:0] inj_a_1755007777446_863,
    input logic [3:0] inj_b_1755007777446_559,
    input logic inj_condition_cc_1755007777446_644,
    input wire [15:0] inj_in_packed_data_1755007777455_220,
    input int inj_in_val_1755007777466_149,
    input logic [15:0] inj_packed_in_1755007777451_912,
    input logic [2:0] inj_sel_in_1755007777459_30,
    input logic [7:0] inj_val1_cc_1755007777446_523,
    input logic [7:0] inj_val2_cc_1755007777446_182,
    input logic [7:0] inj_val3_cc_1755007777446_607,
    input logic [31:0] inj_wide_data_in_1755007777450_810,
    input wire reset,
    output logic inj_data_out_1755007777453_116,
    output reg [7:0] inj_data_out_1755007777459_456,
    output logic inj_dout_1755007777457_246,
    output logic inj_dout_a_1755007777449_811,
    output logic inj_dout_b_1755007777449_94,
    output logic [7:0] inj_field2_o_1755007777451_618,
    output logic inj_o_done_1755007777448_75,
    output wire [7:0] inj_out_byte_1755007777455_737,
    output logic inj_out_m9_1755007777447_627,
    output logic inj_out_n_1755007777447_57,
    output logic inj_out_n_1755007777464_855,
    output logic [7:0] inj_out_reg_cc_1755007777446_351,
    output int inj_out_val_1755007777466_984,
    output logic [7:0] inj_out_val_o_1755007777461_202,
    output logic [3:0] inj_sum_1755007777446_270,
    output bit inj_system_status_clear_1755007777446_534,
    output logic [31:0] inj_wide_data_out_1755007777450_540
);
    // BEGIN: split_conditional_reorder_ts1755007777446
    // BEGIN: PragmaResetDirectives_ts1755007777446
`ifdef SLANG_PRAGMA
`reset protect diagnostic
`endif
    // BEGIN: unsupported_logand_expr_ts1755007777447
    logic [7:0] var_m9_ts1755007777447;
        // BEGIN: mod_basic_ts1755007777448
        logic r_state_ts1755007777448;
            // BEGIN: ModClockedConditional_ts1755007777454
            logic reg_data_ts1755007777453;
                // BEGIN: Module_ControlFlow_ts1755007777459
                reg [7:0] temp_ts1755007777459;
                    // BEGIN: module_in_program_ref_ts1755007777466
                    assign inj_out_val_1755007777466_984 = inj_in_val_1755007777466_149;
                    // END: module_in_program_ref_ts1755007777466

                    // BEGIN: LintParamUnused_ts1755007777464
                    assign inj_out_n_1755007777464_855 = inj_condition_cc_1755007777446_644;
                    // END: LintParamUnused_ts1755007777464

                    split_conditional_blocking split_conditional_blocking_inst_1755007777461_5029 (
                        .out_val_o(inj_out_val_o_1755007777461_202),
                        .condition_o(reg_data_ts1755007777453),
                        .in_false_o(inj_val1_cc_1755007777446_523),
                        .in_true_o(var_m9_ts1755007777447)
                    );
                always_comb begin
                    unique case (inj_sel_in_1755007777459_30)
                        3'b000: temp_ts1755007777459 = inj_val1_cc_1755007777446_523;
                        3'b001: temp_ts1755007777459 = inj_val1_cc_1755007777446_523 + 1;
                        3'b010: temp_ts1755007777459 = inj_val1_cc_1755007777446_523 - 1;
                        default: temp_ts1755007777459 = 8'hAA;
                    endcase
                end
                always_ff @(posedge clk or negedge reset) begin
                    if (!reset)
                        inj_data_out_1755007777459_456 <= 8'h00;
                    else
                        inj_data_out_1755007777459_456 <= temp_ts1755007777459;
                end
                // END: Module_ControlFlow_ts1755007777459

                // BEGIN: ModRegister_ts1755007777457
                always @* begin
                    inj_dout_1755007777457_246 = reg_data_ts1755007777453;
                end
                // END: ModRegister_ts1755007777457

                packed_struct_module packed_struct_module_inst_1755007777455_8663 (
                    .in_packed_data(inj_in_packed_data_1755007777455_220),
                    .out_byte(inj_out_byte_1755007777455_737)
                );
            always @(posedge clk) begin
            if (inj_condition_cc_1755007777446_644) begin
                reg_data_ts1755007777453 <= r_state_ts1755007777448;
            end
            end
            assign inj_data_out_1755007777453_116 = reg_data_ts1755007777453;
            // END: ModClockedConditional_ts1755007777454

            typedef_struct_public_mod typedef_struct_public_mod_inst_1755007777451_2002 (
                .packed_in(inj_packed_in_1755007777451_912),
                .field2_o(inj_field2_o_1755007777451_618)
            );
            // BEGIN: module_using_package_param_ts1755007777450
            assign inj_wide_data_out_1755007777450_540 = inj_wide_data_in_1755007777450_810;
            // END: module_using_package_param_ts1755007777450

            // BEGIN: ModMultipleAlways_ts1755007777449
            always @(posedge clk or negedge reset) begin 
            if (!reset) begin 
                inj_dout_a_1755007777449_811 <= 1'b0;
            end else begin
                inj_dout_a_1755007777449_811 <= r_state_ts1755007777448; 
            end
            end
            always @(posedge clk) begin 
            inj_dout_b_1755007777449_94 <= inj_condition_cc_1755007777446_644; 
            end
            // END: ModMultipleAlways_ts1755007777449

        parameter int PARAM_BASIC = 42;
        always_ff @(posedge clk) begin
            r_state_ts1755007777448 <= ~r_state_ts1755007777448;
        end
        always_comb begin
            inj_o_done_1755007777448_75 = r_state_ts1755007777448;
        end
        // END: mod_basic_ts1755007777448

    always_comb begin
        var_m9_ts1755007777447 = inj_val1_cc_1755007777446_523;
        if ((var_m9_ts1755007777447 > 10) && (inj_val2_cc_1755007777446_182 < 5)) begin
            inj_out_m9_1755007777447_627 = 1;
        end else begin
            inj_out_m9_1755007777447_627 = 0;
        end
        var_m9_ts1755007777447++;
    end
    // END: unsupported_logand_expr_ts1755007777447

    LintParamUnused LintParamUnused_inst_1755007777447_2068 (
        .in_m(inj_condition_cc_1755007777446_644),
        .out_n(inj_out_n_1755007777447_57)
    );
assign inj_system_status_clear_1755007777446_534 = reset;
    // END: PragmaResetDirectives_ts1755007777446

    CombinationalLogicImplicit CombinationalLogicImplicit_inst_1755007777446_810 (
        .b(inj_b_1755007777446_559),
        .sum(inj_sum_1755007777446_270),
        .a(inj_a_1755007777446_863)
    );
    always @(posedge clk) begin
        inj_out_reg_cc_1755007777446_351 <= inj_val1_cc_1755007777446_523;
        if (inj_condition_cc_1755007777446_644) begin
            inj_out_reg_cc_1755007777446_351 <= inj_val2_cc_1755007777446_182;
        end else begin
            inj_out_reg_cc_1755007777446_351 <= inj_val3_cc_1755007777446_607;
        end
    end
    // END: split_conditional_reorder_ts1755007777446
endmodule

