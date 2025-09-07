module BindSimpleModule (
    input bit in,
    output bit out
);
    assign out = in;
endmodule

module DummyBindTarget (
    input bit d_in,
    output bit d_out
);
    assign d_out = d_in;
    BindSimpleModule u_bind (.in(d_in), .out());
endmodule

module GenerateFor (
    input logic [3:0] data_in,
    output logic [3:0] data_out
);
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : g_loop
            assign data_out[i] = data_in[i];
        end
    endgenerate
endmodule

module ModuleBasic (
    input logic a,
    input int b,
    output logic out_a,
    output int out_b
);
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c;
    int   d;
    always_comb begin
        logic temp_v;
        temp_v = d;
        c      = temp_v;
    end
    assign out_a = a;
    assign d     = b;
    assign out_b = d + P1 + LP1;
endmodule

module ModuleGenerateIf (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    parameter int PROCESS_ENABLE = 1;
    logic [7:0] processed_val;
    generate
        if (PROCESS_ENABLE) begin : process_block
            assign processed_val = in_val + 10;
        end else begin : bypass_block
            assign processed_val = in_val;
        end
    endgenerate
    assign out_val = processed_val;
endmodule

module SequentialLogic (
    input logic clk,
    input logic [7:0] data_in,
    input logic rst,
    output logic [7:0] data_out
);
    logic [7:0] internal_reg;
    always @(posedge clk or negedge rst) begin
        if (~rst) begin
            internal_reg <= 8'h00;
        end else begin
            internal_reg <= data_in;
        end
    end
    assign data_out = internal_reg;
endmodule

module mod_case_block_attrs (
    input wire [1:0] i_sel,
    input wire [3:0] i_val,
    output logic [3:0] o_out
);
    logic [3:0] l_temp;
    always_comb begin
        (* full_case *)
        (* parallel_case *)
        case (i_sel)
            2'b00: l_temp = i_val;
            2'b01: l_temp = i_val << 1;
            2'b10: l_temp = i_val >> 1;
            default: l_temp = 4'bxxxx;
        endcase
        (* coverage_off *)
        begin : my_named_block
            o_out = l_temp;
        end
    end
endmodule

module mod_simple_ref (
    input logic i_data,
    output logic o_result
);
    logic internal_sig;
    always_comb begin
        internal_sig = i_data;
        o_result = internal_sig;
    end
endmodule

module multi_always_comb (
    input wire [7:0] in1,
    input wire [7:0] in2,
    output wire [7:0] out1,
    output wire [7:0] out2
);
    logic [7:0] intermediate1;
    logic [7:0] intermediate2;
    always @(*) begin
        intermediate1 = in1 & in2;
    end
    always @(*) begin
        intermediate2 = in1 | in2;
    end
    assign out1 = intermediate1 + 8'd1;
    assign out2 = intermediate2 - 8'd1;
endmodule

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module attributes_on_expr_port (
    input logic i_control,
    input logic i_in,
    output logic o_out
);
    logic internal_sig;
    assign internal_sig = i_in & i_control;
    simple_adder sa_inst(
        .a  (i_in),
        (* fanout_limit = 10 *) .b(i_control),
        .sum(o_out)
    );
endmodule

module top_module_config_dummy (
    input logic i,
    output logic o
);
    assign o = i; 
endmodule

module snippet #(
    parameter int SEL_PARAM = 5,
    parameter int SEL_PARAM = 5
) (
    input wire clk,
    input logic [3:0] inj_a_1755007893405_386,
    input logic [3:0] inj_b_1755007893405_252,
    input bit inj_d_in_1755007893413_841,
    input logic [7:0] inj_data_in_1755007893405_473,
    input logic inj_i_control_1755007893405_740,
    input logic inj_i_in_1755007893405_733,
    input wire [1:0] inj_i_sel_1755007893420_474,
    input wire [3:0] inj_i_val_1755007893420_615,
    input logic [7:0] inj_in1_1755007893408_930,
    input wire [7:0] inj_in1_1755007893456_688,
    input logic [7:0] inj_in2_1755007893408_86,
    input wire [7:0] inj_in2_1755007893456_734,
    input bit [7:0] inj_in_value_1755007893461_184,
    input int inj_sel_in_1755007893406_835,
    input logic [9:0] inj_val_in_1755007893422_143,
    input wire reset,
    output logic [7:0] inj_concat_out_1755007893446_152,
    output bit inj_d_out_1755007893413_682,
    output logic [7:0] inj_data_out_1755007893405_38,
    output logic [7:0] inj_data_out_1755007893406_892,
    output logic [7:0] inj_data_out_1755007893432_704,
    output logic [3:0] inj_data_out_1755007893436_22,
    output logic inj_nand_out_1755007893408_729,
    output logic inj_nm_out_1755007893415_732,
    output logic inj_nor_out_1755007893408_719,
    output logic [7:0] inj_o1_r_1755007893412_912,
    output logic [7:0] inj_o2_r_1755007893412_710,
    output logic [7:0] inj_o3_r_1755007893412_153,
    output logic inj_o_1755007893425_233,
    output logic inj_o_out_1755007893405_940,
    output logic [3:0] inj_o_out_1755007893420_222,
    output logic inj_o_p_and_1755007893410_723,
    output logic inj_o_p_xor_1755007893410_435,
    output logic inj_o_result_1755007893423_641,
    output wire [7:0] inj_out1_1755007893456_721,
    output wire [7:0] inj_out2_1755007893456_883,
    output bit [2:0] inj_out_category_1755007893461_87,
    output logic [15:0] inj_out_concat_1755007893405_546,
    output logic [15:0] inj_out_concat_1755007893427_292,
    output logic inj_out_e_1755007893407_430,
    output logic [3:0] inj_out_h_1755007893430_867,
    output logic inj_out_its_1755007893417_898,
    output logic [3:0] inj_out_l_1755007893430_405,
    output logic inj_out_la_1755007893439_334,
    output logic [7:0] inj_out_val_1755007893409_892,
    output logic [7:0] inj_out_vec_y_1755007893451_806,
    output logic inj_q_1755007893443_490,
    output logic [7:0] inj_result_m_1755007893466_287,
    output logic [9:0] inj_val_out_1755007893422_153,
    output logic inj_xnor_out_1755007893408_352
);
    // BEGIN: ConcatVectorOps_ts1755007893406
    // BEGIN: ModuleHierarchy_Low_ts1755007893407
    ModuleBasic m1 (
        .a     (1'b1),
        .b     (inj_sel_in_1755007893406_835),
        .out_a (),
        .out_b ( )
    );
    if (SEL_PARAM > 5) begin : gen_high
        int high_data_ts1755007893406;
        ModuleBasic m_high (
            .a     (1'b0),
            .b     (SEL_PARAM),
            .out_a (),
            .out_b (high_data_ts1755007893406)
        );
    end else begin : gen_low
        int low_data_ts1755007893406;
        ModuleBasic m_low (
            .a     (1'b0),
            .b     (SEL_PARAM),
            .out_a (),
            .out_b (low_data_ts1755007893406)
        );
    end
    for (genvar i = 0; i < 2; ++i) begin : gen_loop
        logic [1:0] sub_in_ts1755007893406;
        assign sub_in_ts1755007893406 = inj_b_1755007893405_252[i*2 +: 2];
        int temp_int_ts1755007893406;
            // BEGIN: split_complex_blocking_ts1755007893412
            logic [7:0] t1_r_ts1755007893412, t2_r_ts1755007893412;
                // BEGIN: ModuleHierarchy_Low_ts1755007893433
                ModuleBasic m1 (
                    .a     (1'b1),
                    .b     (temp_int_ts1755007893406),
                    .out_a (),
                    .out_b ( )
                );
                if (SEL_PARAM > 5) begin : gen_high
                    int high_data_ts1755007893433;
                    ModuleBasic m_high (
                        .a     (1'b0),
                        .b     (SEL_PARAM),
                        .out_a (),
                        .out_b (high_data_ts1755007893433)
                    );
                end else begin : gen_low
                    int low_data_ts1755007893433;
                    ModuleBasic m_low (
                        .a     (1'b0),
                        .b     (SEL_PARAM),
                        .out_a (),
                        .out_b (low_data_ts1755007893433)
                    );
                end
                for (genvar i = 0; i < 2; ++i) begin : gen_loop
                    logic [1:0] sub_in_ts1755007893433;
                    assign sub_in_ts1755007893433 = inj_b_1755007893405_252[i*2 +: 2];
                    int temp_int_ts1755007893433;
                        // BEGIN: macro_concat_user_ts1755007893447
                        `define MAKE_NAME(a,b) a``b
                        logic var_signal_ts1755007893447;
                            // BEGIN: split_nested_if_ts1755007893466
                            always @(posedge clk) begin
                                if (var_signal_ts1755007893447) begin
                                    if (inj_i_control_1755007893405_740) begin
                                        inj_result_m_1755007893466_287 <= inj_in2_1755007893408_86;
                                    end else begin
                                        inj_result_m_1755007893466_287 <= inj_in1_1755007893408_930;
                                    end
                                end else begin
                                    inj_result_m_1755007893466_287 <= inj_data_in_1755007893405_473;
                                end
                            end
                            // END: split_nested_if_ts1755007893466

                            // BEGIN: mod_if_elseif_chained_ts1755007893461
                        always_comb begin
                            if (inj_in_value_1755007893461_184 < 10) begin
                                inj_out_category_1755007893461_87 = 3'd0;
                            end else if (inj_in_value_1755007893461_184 < 50) begin
                                inj_out_category_1755007893461_87 = 3'd1;
                            end else if (inj_in_value_1755007893461_184 < 100) begin
                                inj_out_category_1755007893461_87 = 3'd2;
                            end else begin
                                inj_out_category_1755007893461_87 = 3'd3;
                            end
                        end
                            // END: mod_if_elseif_chained_ts1755007893461

                            multi_always_comb multi_always_comb_inst_1755007893456_6788 (
                                .out2(inj_out2_1755007893456_883),
                                .in1(inj_in1_1755007893456_688),
                                .in2(inj_in2_1755007893456_734),
                                .out1(inj_out1_1755007893456_721)
                            );
                            // BEGIN: split_vector_assign_ts1755007893452
                            always @(posedge clk) begin
                                if (var_signal_ts1755007893447) begin
                                    inj_out_vec_y_1755007893451_806[3:0] <= t1_r_ts1755007893412[3:0];
                                    inj_out_vec_y_1755007893451_806[7:4] <= t1_r_ts1755007893412[7:4] + 1;
                                end else begin
                                    inj_out_vec_y_1755007893451_806 <= 8'hFF;
                                end
                            end
                            // END: split_vector_assign_ts1755007893452

                        always_comb begin
                            `MAKE_NAME(var,_signal) = inj_b_1755007893405_252[0];
                        end
                        assign inj_concat_out_1755007893446_152 = {4'b0, inj_b_1755007893405_252[3:1], var_signal_ts1755007893447};
                        // END: macro_concat_user_ts1755007893447

                        // BEGIN: basic_d_flipflop_ts1755007893443
                        always_ff @(posedge clk) begin
                            inj_q_1755007893443_490 <= inj_i_in_1755007893405_733;
                        end
                        // END: basic_d_flipflop_ts1755007893443

                        // BEGIN: mod_large_array_target_ts1755007893440
                        assign inj_out_la_1755007893439_334 = inj_i_control_1755007893405_740;
                        // END: mod_large_array_target_ts1755007893440

                        GenerateFor GenerateFor_inst_1755007893436_5599 (
                            .data_in(inj_b_1755007893405_252),
                            .data_out(inj_data_out_1755007893436_22)
                        );
                    ModuleBasic m_inst (
                        .a      (1'b0),
                        .b      (int'(sub_in_ts1755007893433)),
                        .out_a  (),
                        .out_b  (temp_int_ts1755007893433)
                    );
                    assign inj_data_out_1755007893432_704[i*4 +: 4] = temp_int_ts1755007893433[3:0];
                end
                // END: ModuleHierarchy_Low_ts1755007893433

                // BEGIN: concat_assign_ts1755007893430
                assign {inj_out_h_1755007893430_867, inj_out_l_1755007893430_405} = inj_in1_1755007893408_930;
                // END: concat_assign_ts1755007893430

                // BEGIN: ComplexConversions_ts1755007893428
                always_comb begin
                    inj_out_concat_1755007893427_292 = {inj_data_in_1755007893405_473, t2_r_ts1755007893412};
                end
                // END: ComplexConversions_ts1755007893428

                top_module_config_dummy top_module_config_dummy_inst_1755007893425_6201 (
                    .i(inj_i_in_1755007893405_733),
                    .o(inj_o_1755007893425_233)
                );
                mod_simple_ref mod_simple_ref_inst_1755007893423_48 (
                    .i_data(inj_i_control_1755007893405_740),
                    .o_result(inj_o_result_1755007893423_641)
                );
                // BEGIN: SimpleAssign_ts1755007893422
                assign inj_val_out_1755007893422_153 = inj_val_in_1755007893422_143;
                // END: SimpleAssign_ts1755007893422

                mod_case_block_attrs mod_case_block_attrs_inst_1755007893420_976 (
                    .i_sel(inj_i_sel_1755007893420_474),
                    .i_val(inj_i_val_1755007893420_615),
                    .o_out(inj_o_out_1755007893420_222)
                );
                // BEGIN: ImplicitTimeScaleModule_ts1755007893418
                assign inj_out_its_1755007893417_898 = inj_i_in_1755007893405_733;
                // END: ImplicitTimeScaleModule_ts1755007893418

                // BEGIN: nested_module_ts1755007893415
                assign inj_nm_out_1755007893415_732 = inj_i_control_1755007893405_740;
                // END: nested_module_ts1755007893415

                DummyBindTarget DummyBindTarget_inst_1755007893413_5715 (
                    .d_in(inj_d_in_1755007893413_841),
                    .d_out(inj_d_out_1755007893413_682)
                );
            always @(*) begin
                t1_r_ts1755007893412 = inj_data_in_1755007893405_473 + inj_in2_1755007893408_86;
                inj_o1_r_1755007893412_912 = t1_r_ts1755007893412 - inj_in1_1755007893408_930;
                t2_r_ts1755007893412 = inj_in2_1755007893408_86 * inj_in1_1755007893408_930;
                inj_o2_r_1755007893412_710 = t1_r_ts1755007893412 + t2_r_ts1755007893412;
                inj_o3_r_1755007893412_153 = t2_r_ts1755007893412 / 2;
            end
            // END: split_complex_blocking_ts1755007893412

            // BEGIN: primitive_example_ts1755007893411
            and (inj_o_p_and_1755007893410_723, inj_i_in_1755007893405_733, inj_i_control_1755007893405_740);
            xor (inj_o_p_xor_1755007893410_435, inj_i_in_1755007893405_733, inj_i_control_1755007893405_740);
            // END: primitive_example_ts1755007893411

            ModuleGenerateIf ModuleGenerateIf_inst_1755007893409_758 (
                .out_val(inj_out_val_1755007893409_892),
                .in_val(inj_in1_1755007893408_930)
            );
            // BEGIN: remaining_reduction_ops_ts1755007893408
            assign inj_nand_out_1755007893408_729 = ~&inj_in1_1755007893408_930;
            assign inj_nor_out_1755007893408_719 = ~|inj_in2_1755007893408_86;
            assign inj_xnor_out_1755007893408_352 = ^~inj_data_in_1755007893405_473;
            // END: remaining_reduction_ops_ts1755007893408

            // BEGIN: LintCombBlockAssign_ts1755007893407
            always_comb begin
                inj_out_e_1755007893407_430 = inj_i_in_1755007893405_733 & inj_i_control_1755007893405_740;
            end
            // END: LintCombBlockAssign_ts1755007893407

        ModuleBasic m_inst (
            .a      (1'b0),
            .b      (int'(sub_in_ts1755007893406)),
            .out_a  (),
            .out_b  (temp_int_ts1755007893406)
        );
        assign inj_data_out_1755007893406_892[i*4 +: 4] = temp_int_ts1755007893406[3:0];
    end
    // END: ModuleHierarchy_Low_ts1755007893407

    assign inj_out_concat_1755007893405_546 = {inj_a_1755007893405_386, inj_b_1755007893405_252, inj_data_in_1755007893405_473};
    // END: ConcatVectorOps_ts1755007893406

    SequentialLogic SequentialLogic_inst_1755007893405_6784 (
        .data_in(inj_data_in_1755007893405_473),
        .rst(reset),
        .data_out(inj_data_out_1755007893405_38),
        .clk(clk)
    );
    attributes_on_expr_port attributes_on_expr_port_inst_1755007893405_1616 (
        .i_control(inj_i_control_1755007893405_740),
        .i_in(inj_i_in_1755007893405_733),
        .o_out(inj_o_out_1755007893405_940)
    );
endmodule

