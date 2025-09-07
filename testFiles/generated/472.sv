module CaseEq (
    output wire match_x_neq,
    output wire match_z_eq,
    inout wire [3:0] data_io
);
    assign match_z_eq = (data_io === 4'b101z);
    assign match_x_neq = (data_io !== 4'b1x0x);
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

module PragmaOnceDirective (
    input bit trigger_input,
    output bit trigger_output
);
assign trigger_output = trigger_input;
endmodule

module mod_fixup_target (
    input logic fs_in_target,
    output logic fs_out_target
);
    assign fs_out_target = fs_in_target;
endmodule

module wide_ops_deep (
    input logic [63:0] wide_a,
    input logic [63:0] wide_b,
    input logic [63:0] wide_c,
    output logic [63:0] wide_out
);
    assign wide_out = (((wide_a + wide_b) ^ wide_c) & (~wide_a | wide_b)) + (wide_c >>> 5);
endmodule

module snippet #(
    parameter int SEL_PARAM = 5
) (
    input wire clk,
    input logic [3:0] inj_data_in_1755007912009_100,
    input bit [7:0] inj_data_in_1755007912022_697,
    input bit inj_dummy_in_1755007912011_705,
    input logic inj_fs_in_target_1755007912009_555,
    input logic [7:0] inj_in_a_1755007912015_330,
    input logic [7:0] inj_in_b_1755007912015_690,
    input int inj_sel_in_1755007912009_644,
    input logic [63:0] inj_wide_a_1755007912020_996,
    input logic [63:0] inj_wide_b_1755007912020_437,
    input logic [63:0] inj_wide_c_1755007912020_78,
    input wire reset,
    output logic [7:0] inj_data_out_1755007912009_376,
    output bit [7:0] inj_data_out_1755007912022_931,
    output int inj_driven_var_1755007912012_510,
    output bit inj_dummy_out_1755007912011_648,
    output bit inj_dummy_out_1755007912013_250,
    output logic inj_fs_out_target_1755007912009_975,
    output wire inj_match_x_neq_1755007912009_49,
    output wire inj_match_z_eq_1755007912009_567,
    output wire inj_o_1755007912009_664,
    output logic inj_out_bit_1755007912016_616,
    output logic [15:0] inj_out_concat_1755007912015_842,
    output bit inj_trigger_output_1755007912018_814,
    output logic [63:0] inj_wide_out_1755007912020_457,
    inout wire [3:0] inj_data_io_1755007912009_532
);
    // BEGIN: buf_primitive_ts1755007912009
    // BEGIN: ModuleHierarchy_Low_ts1755007912010
    ModuleBasic m1 (
        .a     (1'b1),
        .b     (inj_sel_in_1755007912009_644),
        .out_a (),
        .out_b ( )
    );
    if (SEL_PARAM > 5) begin : gen_high
        int high_data_ts1755007912010;
        ModuleBasic m_high (
            .a     (1'b0),
            .b     (SEL_PARAM),
            .out_a (),
            .out_b (high_data_ts1755007912010)
        );
    end else begin : gen_low
        int low_data_ts1755007912010;
        ModuleBasic m_low (
            .a     (1'b0),
            .b     (SEL_PARAM),
            .out_a (),
            .out_b (low_data_ts1755007912010)
        );
    end
    for (genvar i = 0; i < 2; ++i) begin : gen_loop
        logic [1:0] sub_in_ts1755007912010;
        assign sub_in_ts1755007912010 = inj_data_in_1755007912009_100[i*2 +: 2];
        int temp_int_ts1755007912010;
            // BEGIN: m_driver_check_ts1755007912012
            int my_driven_var_ts1755007912012;
                // BEGIN: SimpleLogicTest_ts1755007912022
                logic [7:0] temp_data_ts1755007912022;
                always_comb begin
                    if (inj_dummy_in_1755007912011_705) begin
                        temp_data_ts1755007912022 = inj_data_in_1755007912022_697 + 1;
                    end else begin
                        temp_data_ts1755007912022 = inj_data_in_1755007912022_697 - 1;
                    end
                    inj_data_out_1755007912022_931 = temp_data_ts1755007912022;
                end
                // END: SimpleLogicTest_ts1755007912022

                wide_ops_deep wide_ops_deep_inst_1755007912020_26 (
                    .wide_out(inj_wide_out_1755007912020_457),
                    .wide_a(inj_wide_a_1755007912020_996),
                    .wide_b(inj_wide_b_1755007912020_437),
                    .wide_c(inj_wide_c_1755007912020_78)
                );
                PragmaOnceDirective PragmaOnceDirective_inst_1755007912018_6845 (
                    .trigger_input(inj_dummy_in_1755007912011_705),
                    .trigger_output(inj_trigger_output_1755007912018_814)
                );
                // BEGIN: recursive_macro_dummy_ts1755007912016
                `define RECURSIVE_TEST `RECURSIVE_TEST
                assign inj_out_bit_1755007912016_616 = inj_fs_in_target_1755007912009_555;
                // END: recursive_macro_dummy_ts1755007912016

                // BEGIN: ComplexConversions_ts1755007912015
                always_comb begin
                    inj_out_concat_1755007912015_842 = {inj_in_a_1755007912015_330, inj_in_b_1755007912015_690};
                end
                // END: ComplexConversions_ts1755007912015

                // BEGIN: module_finish_numbers_ts1755007912013
                parameter p_finish_0 = 0;
                parameter p_finish_1 = 1;
                parameter p_finish_2 = 2;
                parameter p_finish_other_3 = 3;
                parameter p_finish_large_100 = 100;
                parameter p_finish_neg_minus1 = -1;
                localparam lp_finish_0 = 0;
                localparam lp_finish_1 = 1;
                localparam lp_finish_2 = 2;
                localparam lp_finish_other_5 = 5;
                localparam lp_finish_neg_minus10 = -10;
                assign inj_dummy_out_1755007912013_250 = inj_dummy_in_1755007912011_705;
                // END: module_finish_numbers_ts1755007912013

            function automatic void write_to_var(input int val);
                my_driven_var_ts1755007912012 = val;
            endfunction
            always @(posedge clk) begin
                write_to_var(temp_int_ts1755007912010);
            end
            assign inj_driven_var_1755007912012_510 = my_driven_var_ts1755007912012;
            // END: m_driver_check_ts1755007912012

            // BEGIN: module_finish_numbers_ts1755007912011
            parameter p_finish_0 = 0;
            parameter p_finish_1 = 1;
            parameter p_finish_2 = 2;
            parameter p_finish_other_3 = 3;
            parameter p_finish_large_100 = 100;
            parameter p_finish_neg_minus1 = -1;
            localparam lp_finish_0 = 0;
            localparam lp_finish_1 = 1;
            localparam lp_finish_2 = 2;
            localparam lp_finish_other_5 = 5;
            localparam lp_finish_neg_minus10 = -10;
            assign inj_dummy_out_1755007912011_648 = inj_dummy_in_1755007912011_705;
            // END: module_finish_numbers_ts1755007912011

        ModuleBasic m_inst (
            .a      (1'b0),
            .b      (int'(sub_in_ts1755007912010)),
            .out_a  (),
            .out_b  (temp_int_ts1755007912010)
        );
        assign inj_data_out_1755007912009_376[i*4 +: 4] = temp_int_ts1755007912010[3:0];
    end
    // END: ModuleHierarchy_Low_ts1755007912010

    mod_fixup_target mod_fixup_target_inst_1755007912009_9400 (
        .fs_out_target(inj_fs_out_target_1755007912009_975),
        .fs_in_target(inj_fs_in_target_1755007912009_555)
    );
    buf b1 (inj_o_1755007912009_664, clk);
    // END: buf_primitive_ts1755007912009

    CaseEq CaseEq_inst_1755007912009_5789 (
        .data_io(inj_data_io_1755007912009_532),
        .match_x_neq(inj_match_x_neq_1755007912009_49),
        .match_z_eq(inj_match_z_eq_1755007912009_567)
    );
endmodule

