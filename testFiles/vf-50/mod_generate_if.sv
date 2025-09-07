module AlwaysCombInvert (
    input logic [3:0] a,
    output logic [3:0] y
);
    always_comb y = ~a;
endmodule

module another_module_config_dummy (
    input logic i,
    output logic o
);
    assign o = i & i; 
endmodule

module cast_select_demo (
    input logic [7:0] in_data,
    output logic [1:0] out_bits
);
    logic [7:0] internal;
    always_comb begin
        internal = in_data;
        out_bits = internal[3 -: 2];
    end
endmodule

module simple_comb (
    input wire [7:0] in_data,
    output wire [7:0] out_data
);
    wire [7:0] intermediate_a;
    wire [7:0] intermediate_b;
    wire [7:0] intermediate_c;
    assign intermediate_a = in_data + 8'd1;
    assign intermediate_b = intermediate_a << 1;
    assign intermediate_c = intermediate_a >> 1;
    assign out_data = intermediate_b | intermediate_c;
endmodule

module split_multiple_blocking (
    input logic [3:0] data_in_n,
    output logic [3:0] data_out1_n,
    output logic [3:0] data_out2_n
);
    logic [3:0] temp_n;
    always @(*) begin
        temp_n = data_in_n + 1;
        data_out1_n = temp_n * 2;
        data_out2_n = temp_n + 3;
    end
endmodule

module top_module_config_dummy (
    input logic i,
    output logic o
);
    assign o = i; 
endmodule

module mod_generate_if (
    input wire clk,
    input logic i_a,
    input logic i_b,
    input logic i_select,
    input logic [3:0] inj_data_in_n_1755538535273_7,
    input wire [2:0] inj_in_index_1755538535274_198,
    input wire [1:0] inj_in_part_lsb_1755538535274_233,
    input wire [7:0] inj_in_vector_1755538535274_771,
    input logic [7:0] inj_v1_x_1755538535280_425,
    input logic [7:0] inj_v2_x_1755538535280_937,
    input logic [7:0] inj_v3_x_1755538535280_384,
    input wire rst,
    output logic [3:0] inj_data_out1_n_1755538535273_185,
    output logic [3:0] inj_data_out2_n_1755538535273_940,
    output logic inj_data_out_1755538535276_110,
    output logic inj_data_out_1755538535277_304,
    output logic [7:0] inj_final_val_1755538535275_921,
    output wire inj_match_x_neq_1755538535288_145,
    output wire inj_match_z_eq_1755538535288_951,
    output logic inj_o_1755538535291_577,
    output logic inj_o_1755538535294_281,
    output logic inj_out_bit_select_1755538535274_607,
    output logic [1:0] inj_out_bits_1755538535283_70,
    output logic [7:0] inj_out_bitwise_ops_1755538535274_670,
    output wire [7:0] inj_out_data_1755538535286_46,
    output logic [3:0] inj_out_part_select_1755538535274_41,
    output logic [7:0] inj_out_vector_assign_1755538535274_174,
    output logic [7:0] inj_out_x_1755538535280_780,
    output logic [3:0] inj_y_1755538535279_170,
    output logic o_mux_out,
    inout wire [3:0] inj_data_io_1755538535288_359
);
    logic internal_common;
    generate
        if (1) begin : gen_true
            logic internal_true;
                // BEGIN: loop_with_internal_assign_ts1755538535275
                logic [7:0] current_val_ts1755538535275;
                    // BEGIN: ModClockedConditional_ts1755538535276
                    logic reg_data_ts1755538535276;
                        another_module_config_dummy another_module_config_dummy_inst_1755538535294_7187 (
                            .i(internal_true),
                            .o(inj_o_1755538535294_281)
                        );
                        top_module_config_dummy top_module_config_dummy_inst_1755538535291_2888 (
                            .o(inj_o_1755538535291_577),
                            .i(reg_data_ts1755538535276)
                        );
                        // BEGIN: CaseEq_ts1755538535288
                        assign inj_match_z_eq_1755538535288_951 = (inj_data_io_1755538535288_359 === 4'b101z);
                        assign inj_match_x_neq_1755538535288_145 = (inj_data_io_1755538535288_359 !== 4'b1x0x);
                        // END: CaseEq_ts1755538535288

                        simple_comb simple_comb_inst_1755538535286_3877 (
                            .out_data(inj_out_data_1755538535286_46),
                            .in_data(inj_in_vector_1755538535274_771)
                        );
                        cast_select_demo cast_select_demo_inst_1755538535283_1170 (
                            .in_data(current_val_ts1755538535275),
                            .out_bits(inj_out_bits_1755538535283_70)
                        );
                        // BEGIN: split_ifelse_chain_ts1755538535281
                        always @(posedge clk) begin
                            if (internal_common) begin
                                inj_out_x_1755538535280_780 <= inj_v1_x_1755538535280_425;
                            end else if (i_b) begin
                                inj_out_x_1755538535280_780 <= inj_v2_x_1755538535280_937;
                            end else if (reg_data_ts1755538535276) begin
                                inj_out_x_1755538535280_780 <= inj_v3_x_1755538535280_384;
                            end else begin
                                inj_out_x_1755538535280_780 <= current_val_ts1755538535275;
                            end
                        end
                        // END: split_ifelse_chain_ts1755538535281

                        AlwaysCombInvert AlwaysCombInvert_inst_1755538535279_6717 (
                            .y(inj_y_1755538535279_170),
                            .a(inj_data_in_n_1755538535273_7)
                        );
                        // BEGIN: sequential_register_ts1755538535277
                        always_ff @(posedge clk or negedge rst) begin
                            if (!rst) begin
                                inj_data_out_1755538535277_304 <= 1'b0; 
                            end else if (i_a) begin
                                inj_data_out_1755538535277_304 <= i_select; 
                            end
                        end
                        // END: sequential_register_ts1755538535277

                    always @(posedge clk) begin
                    if (i_select) begin
                        reg_data_ts1755538535276 <= i_b;
                    end
                    end
                    assign inj_data_out_1755538535276_110 = reg_data_ts1755538535276;
                    // END: ModClockedConditional_ts1755538535276

                always_comb begin
                    current_val_ts1755538535275 = inj_data_in_n_1755538535273_7;
                    for (int k = 0; k < 3; k = k + 1) begin
                        current_val_ts1755538535275 = current_val_ts1755538535275 + 1;
                    end
                    inj_final_val_1755538535275_921 = current_val_ts1755538535275;
                end
                // END: loop_with_internal_assign_ts1755538535275

                // BEGIN: module_selection_ts1755538535274
                always_comb begin
                inj_out_vector_assign_1755538535274_174 = inj_in_vector_1755538535274_771;
                inj_out_bit_select_1755538535274_607 = inj_in_vector_1755538535274_771[inj_in_index_1755538535274_198];
                inj_out_part_select_1755538535274_41 = inj_in_vector_1755538535274_771[inj_in_part_lsb_1755538535274_233 +: 4];
                inj_out_bitwise_ops_1755538535274_670 = inj_in_vector_1755538535274_771 & {8{clk}};
                end
                // END: module_selection_ts1755538535274

                split_multiple_blocking split_multiple_blocking_inst_1755538535273_7549 (
                    .data_in_n(inj_data_in_n_1755538535273_7),
                    .data_out1_n(inj_data_out1_n_1755538535273_185),
                    .data_out2_n(inj_data_out2_n_1755538535273_940)
                );
            always_comb begin
                internal_true = i_a;
                o_mux_out = internal_true;
                internal_common = 1'b1;
            end
        end else begin : gen_false
            logic internal_false;
        end
    endgenerate
    always_comb begin
        internal_common = internal_common ^ i_select;
    end
endmodule

