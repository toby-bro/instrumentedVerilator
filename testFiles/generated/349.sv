interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module Comb_Case (
    input wire [3:0] in0,
    input wire [3:0] in1,
    input wire [3:0] in2,
    input wire [3:0] in3,
    input wire [1:0] sel,
    output reg [3:0] mux_out
);
    always_comb begin
        case (sel)
            2'b00: mux_out = in0;
            2'b01: mux_out = in1;
            2'b10: mux_out = in2;
            default: mux_out = in3;
        endcase
    end
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

module comb_conditional (
    input bit [7:0] data1,
    input bit [7:0] data2,
    input bit sel,
    output bit [7:0] result1,
    output bit [7:0] result2
);
    always @* begin
        if (sel) begin
            result1 = data1;
            result2 = data1;
        end else begin
            result1 = data2;
            result2 = data2;
        end
    end
endmodule

module mod_module_attrs #(
    parameter int WIDTH = 8
) (
    input wire [7:0] i_in,
    output logic [7:0] o_out
);
    logic [WIDTH-1:0] r_data;
    always_comb begin
        r_data = i_in;
    end
    assign o_out = r_data;
endmodule

module mod_split_multiple_vars (
    input logic clk,
    input logic [7:0] data_in,
    input logic reset,
    output logic [7:0] out_mv_a,
    output logic [7:0] out_mv_b,
    output logic [7:0] out_mv_c
);
    logic [7:0]  split_mv_var;
    logic [7:0] other_mv_var1;
    logic [7:0] other_mv_var2;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_mv_var <= 8'b0;
            other_mv_var1 <= 8'b0;
            other_mv_var2 <= 8'b0;
        end else begin
            split_mv_var <= data_in;
            other_mv_var1 <= data_in + 1;
            other_mv_var2 <= data_in + 2;
            if (data_in > 100) begin
                split_mv_var <= 8'hFF;
            end
            out_mv_a <= split_mv_var;
            out_mv_b <= other_mv_var1;
            out_mv_c <= other_mv_var2;
        end
    end
endmodule

module simple_logic_b (
    input wire data_c,
    output wire data_d
);
    assign data_d = data_c;
endmodule

module split_inputs_outputs_only (
    input logic [7:0] in_val_a_l,
    input logic [7:0] in_val_b_l,
    output logic [8:0] out_val_c_l,
    output logic [7:0] out_val_d_l
);
    always @(*) begin
        out_val_c_l = in_val_a_l + in_val_b_l;
        out_val_d_l = in_val_a_l - in_val_b_l;
    end
endmodule

module variable_sel_mux (
    input logic [7:0] in,
    input logic [2:0] index,
    output logic out
);
    assign out = in[index];
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
    parameter int SEL_PARAM = 6
) (
    input wire clk,
    input bit inj_condition_m10_1755007871546_330,
    input logic inj_control_in_1755007871546_44,
    input bit [7:0] inj_data1_1755007871557_112,
    input bit [7:0] inj_data2_1755007871557_463,
    input logic [7:0] inj_data_in_1755007871544_41,
    input logic [3:0] inj_data_in_1755007871551_231,
    input wire [31:0] inj_data_in_1755007871614_715,
    input logic inj_data_ref_in_1755007871546_494,
    input wire [7:0] inj_i_in_1755007871549_563,
    input wire [3:0] inj_in0_1755007871545_19,
    input wire [3:0] inj_in1_1755007871545_240,
    input wire [3:0] inj_in2_1755007871545_6,
    input wire [3:0] inj_in3_1755007871545_289,
    input wire [7:0] inj_in_val1_1755007871601_825,
    input logic [2:0] inj_index_1755007871545_985,
    input logic [15:0] inj_packed_in_1755007871648_561,
    input logic [1:0] inj_sel_1755007871545_190,
    input wire [1:0] inj_sel_1755007871545_224,
    input int inj_sel_in_1755007871551_866,
    input logic [63:0] inj_wide_a_1755007871574_156,
    input logic [63:0] inj_wide_b_1755007871574_432,
    input logic [63:0] inj_wide_c_1755007871574_0,
    input wire reset,
    output wire inj_data_d_1755007871629_75,
    output logic [7:0] inj_data_out_1755007871551_969,
    output logic [31:0] inj_data_out_1755007871614_672,
    output logic inj_data_ref_out_1755007871546_964,
    output int inj_driven_var_1755007871581_958,
    output logic [7:0] inj_field2_o_1755007871648_472,
    output reg [3:0] inj_mux_out_1755007871545_164,
    output logic inj_o_forceable_signal_1755007871564_735,
    output logic [7:0] inj_o_out_1755007871549_73,
    output logic inj_o_read_signal_1755007871564_124,
    output logic inj_out_1755007871545_355,
    output logic inj_out_1755007871607_112,
    output logic [7:0] inj_out_case_a_1755007871544_252,
    output logic [7:0] inj_out_case_b_1755007871544_628,
    output logic inj_out_data_q_1755007871554_777,
    output logic [7:0] inj_out_if_a_1755007871568_104,
    output logic [7:0] inj_out_if_b_1755007871569_238,
    output logic inj_out_m9_1755007871643_448,
    output logic [7:0] inj_out_mv_a_1755007871547_176,
    output logic [7:0] inj_out_mv_b_1755007871547_737,
    output logic [7:0] inj_out_mv_c_1755007871547_949,
    output logic [7:0] inj_out_ternary_result_1755007871601_359,
    output int inj_out_val_1755007871637_899,
    output logic [8:0] inj_out_val_c_l_1755007871621_735,
    output logic [8:0] inj_out_val_c_l_1755007871633_638,
    output logic [7:0] inj_out_val_d_l_1755007871621_662,
    output logic [7:0] inj_out_val_d_l_1755007871633_882,
    output logic [7:0] inj_out_val_m10_1755007871546_405,
    output logic inj_out_wire_1755007871548_204,
    output logic inj_q_1755007871560_113,
    output bit [7:0] inj_result1_1755007871557_727,
    output bit [7:0] inj_result2_1755007871557_492,
    output logic inj_status_out_1755007871546_490,
    output bit inj_system_status_clear_1755007871593_899,
    output logic [63:0] inj_wide_out_1755007871574_655,
    output logic [63:0] inj_wide_out_1755007871587_266,
    inout wire inj_data_inout_1755007871546_886
);
    // BEGIN: mod_split_case_ts1755007871545
    logic [7:0]  split_case_var_ts1755007871545;
    logic [7:0] other_case_var_ts1755007871545;
        // BEGIN: unsupported_cond_expr_ts1755007871546
        logic [7:0] var_m10_ts1755007871546;
            // BEGIN: ModuleHierarchy_High_ts1755007871552
            ModuleBasic m1 (
                .a      (1'b1),
                .b      (inj_sel_in_1755007871551_866),
                .out_a  (),
                .out_b  ( )
            );
            if (SEL_PARAM > 5) begin : gen_high
                int high_data_ts1755007871551;
                ModuleBasic m_high (
                    .a      (1'b0),
                    .b      (SEL_PARAM),
                    .out_a  (),
                    .out_b  (high_data_ts1755007871551)
                );
            end else begin : gen_low
                int low_data_ts1755007871551;
                ModuleBasic m_low (
                    .a      (1'b0),
                    .b      (SEL_PARAM),
                    .out_a  (),
                    .out_b  (low_data_ts1755007871551)
                );
            end
            for (genvar i = 0; i < 2; ++i) begin : gen_loop
                logic [1:0] sub_in_ts1755007871551;
                assign sub_in_ts1755007871551 = inj_data_in_1755007871551_231[i*2 +: 2];
                int temp_int_ts1755007871551;
                    // BEGIN: module_assign_nonblocking_ts1755007871554
                    my_if vif_inst();
                    logic [7:0] data_q_ts1755007871554;
                        // BEGIN: module_forceable_attr_ts1755007871565
                        logic forceable_signal_ts1755007871564 ;
                        logic read_internal_ts1755007871564;
                            // BEGIN: mod_split_if_ts1755007871569
                            logic [7:0]  split_if_var_ts1755007871569;
                            logic [7:0] other_if_var_ts1755007871569;
                                // BEGIN: m_driver_check_ts1755007871582
                                int my_driven_var_ts1755007871582;
                                    // BEGIN: mod_part_select_ts1755007871614
                                    logic [31:0] temp_reg_ts1755007871614;
                                        // BEGIN: nested_macro_expansion_ts1755007871638
                                        `define LVL1(x) ((x) + 1)
                                        `define LVL2(y) `LVL1((y) * 2)
                                        `define LVL3(z) `LVL2((z) / 3)
                                        int nested_result_ts1755007871638;
                                            // BEGIN: unsupported_logand_expr_ts1755007871643
                                            logic [7:0] var_m9_ts1755007871643;
                                                // BEGIN: typedef_struct_public_mod_ts1755007871649
                                                typedef struct packed {
                                                    logic [7:0] field1_ts1755007871649;
                                                    logic [7:0] field2_ts1755007871649;
                                                } my_public_packed_struct_t;
                                                my_public_packed_struct_t my_struct_var;
                                                always_comb begin
                                                    my_struct_var = inj_packed_in_1755007871648_561;
                                                end
                                                assign inj_field2_o_1755007871648_472 = my_struct_var.field2_ts1755007871649;
                                                // END: typedef_struct_public_mod_ts1755007871649

                                            always_comb begin
                                                var_m9_ts1755007871643 = data_q_ts1755007871554;
                                                if ((var_m9_ts1755007871643 > 10) && (split_case_var_ts1755007871545 < 5)) begin
                                                    inj_out_m9_1755007871643_448 = 1;
                                                end else begin
                                                    inj_out_m9_1755007871643_448 = 0;
                                                end
                                                var_m9_ts1755007871643++;
                                            end
                                            // END: unsupported_logand_expr_ts1755007871643

                                        always_comb begin
                                            nested_result_ts1755007871638 = `LVL3(`LVL1(temp_int_ts1755007871551));
                                        end
                                        assign inj_out_val_1755007871637_899 = nested_result_ts1755007871638;
                                        // END: nested_macro_expansion_ts1755007871638

                                        // BEGIN: split_inputs_outputs_only_ts1755007871633
                                        always @(*) begin
                                            inj_out_val_c_l_1755007871633_638 = other_if_var_ts1755007871569 + data_q_ts1755007871554;
                                            inj_out_val_d_l_1755007871633_882 = other_if_var_ts1755007871569 - data_q_ts1755007871554;
                                        end
                                        // END: split_inputs_outputs_only_ts1755007871633

                                        simple_logic_b simple_logic_b_inst_1755007871629_1009 (
                                            .data_c(clk),
                                            .data_d(inj_data_d_1755007871629_75)
                                        );
                                        split_inputs_outputs_only split_inputs_outputs_only_inst_1755007871621_112 (
                                            .out_val_c_l(inj_out_val_c_l_1755007871621_735),
                                            .out_val_d_l(inj_out_val_d_l_1755007871621_662),
                                            .in_val_a_l(split_if_var_ts1755007871569),
                                            .in_val_b_l(other_if_var_ts1755007871569)
                                        );
                                    always_comb begin
                                        temp_reg_ts1755007871614[7:0] = inj_data_in_1755007871614_715[7:0];
                                        temp_reg_ts1755007871614[15:8] = inj_data_in_1755007871614_715[23:16];
                                        temp_reg_ts1755007871614[31:16] = inj_data_in_1755007871614_715[15:0];
                                        temp_reg_ts1755007871614[0] = inj_data_in_1755007871614_715[31];
                                        temp_reg_ts1755007871614[8] = inj_data_in_1755007871614_715[0];
                                        inj_data_out_1755007871614_672 = temp_reg_ts1755007871614;
                                    end
                                    // END: mod_part_select_ts1755007871614

                                    // BEGIN: simple_and_gate_ts1755007871607
                                    assign inj_out_1755007871607_112 = inj_control_in_1755007871546_44 & forceable_signal_ts1755007871564;
                                    // END: simple_and_gate_ts1755007871607

                                    // BEGIN: module_ternary_ts1755007871601
                                    always_comb begin
                                    inj_out_ternary_result_1755007871601_359 = reset ? inj_in_val1_1755007871601_825 : inj_i_in_1755007871549_563;
                                    end
                                    // END: module_ternary_ts1755007871601

                                    // BEGIN: PragmaResetDirectives_ts1755007871593
                                `ifdef SLANG_PRAGMA
                                `reset protect diagnostic
                                `endif
                                assign inj_system_status_clear_1755007871593_899 = reset;
                                    // END: PragmaResetDirectives_ts1755007871593

                                    wide_ops_deep wide_ops_deep_inst_1755007871587_5690 (
                                        .wide_out(inj_wide_out_1755007871587_266),
                                        .wide_a(inj_wide_c_1755007871574_0),
                                        .wide_b(inj_wide_b_1755007871574_432),
                                        .wide_c(inj_wide_a_1755007871574_156)
                                    );
                                function automatic void write_to_var(input int val);
                                    my_driven_var_ts1755007871582 = val;
                                endfunction
                                always @(posedge clk) begin
                                    write_to_var(temp_int_ts1755007871551);
                                end
                                assign inj_driven_var_1755007871581_958 = my_driven_var_ts1755007871582;
                                // END: m_driver_check_ts1755007871582

                                // BEGIN: wide_ops_deep_ts1755007871574
                                assign inj_wide_out_1755007871574_655 = (((inj_wide_a_1755007871574_156 + inj_wide_b_1755007871574_432) ^ inj_wide_c_1755007871574_0) & (~inj_wide_a_1755007871574_156 | inj_wide_b_1755007871574_432)) + (inj_wide_c_1755007871574_0 >>> 5);
                                // END: wide_ops_deep_ts1755007871574

                            always_ff @(posedge clk or posedge reset) begin
                                if (reset) begin
                                    split_if_var_ts1755007871569 <= 8'b0;
                                    other_if_var_ts1755007871569 <= 8'b0;
                                end else begin
                                    if (inj_data_ref_in_1755007871546_494) begin
                                        split_if_var_ts1755007871569 <= var_m10_ts1755007871546;
                                        other_if_var_ts1755007871569 <= var_m10_ts1755007871546 + 3;
                                    end else begin
                                        split_if_var_ts1755007871569 <= var_m10_ts1755007871546 - 1;
                                        other_if_var_ts1755007871569 <= var_m10_ts1755007871546 - 2;
                                    end
                                end
                            end
                            always_comb begin
                                inj_out_if_a_1755007871568_104 = split_if_var_ts1755007871569;
                                inj_out_if_b_1755007871569_238 = other_if_var_ts1755007871569;
                            end
                            // END: mod_split_if_ts1755007871569

                        assign inj_o_forceable_signal_1755007871564_735 = forceable_signal_ts1755007871564;
                        always @(posedge clk or negedge reset) begin
                            if (!reset) begin
                                forceable_signal_ts1755007871564 <= 1'b0;
                                read_internal_ts1755007871564 <= 1'b0;
                            end else begin
                                if (inj_data_ref_in_1755007871546_494) begin
                                    forceable_signal_ts1755007871564 <= inj_control_in_1755007871546_44;
                                end
                                read_internal_ts1755007871564 <= forceable_signal_ts1755007871564;
                            end
                        end
                        assign inj_o_read_signal_1755007871564_124 = read_internal_ts1755007871564;
                        // END: module_forceable_attr_ts1755007871565

                        // BEGIN: ModClockedResetReg_ts1755007871561
                        always @(posedge clk or negedge reset) begin
                        if (!reset) begin
                            inj_q_1755007871560_113 <= 1'b0;
                        end else begin
                            inj_q_1755007871560_113 <= inj_data_ref_in_1755007871546_494;
                        end
                        end
                        // END: ModClockedResetReg_ts1755007871561

                        comb_conditional comb_conditional_inst_1755007871557_2433 (
                            .result2(inj_result2_1755007871557_492),
                            .data1(inj_data1_1755007871557_112),
                            .data2(inj_data2_1755007871557_463),
                            .sel(inj_condition_m10_1755007871546_330),
                            .result1(inj_result1_1755007871557_727)
                        );
                    always_ff @(posedge clk or posedge reset) begin
                        if (reset) begin
                            vif_inst.data <= 8'h0;
                            data_q_ts1755007871554 <= 8'h0;
                        end else begin
                            vif_inst.data <= other_case_var_ts1755007871545;
                            data_q_ts1755007871554 <= vif_inst.data;
                        end
                    end
                    assign inj_out_data_q_1755007871554_777 = data_q_ts1755007871554;
                    // END: module_assign_nonblocking_ts1755007871554

                ModuleBasic m_inst (
                    .a      (1'b0),
                    .b      (int'(sub_in_ts1755007871551)),
                    .out_a  (),
                    .out_b  (temp_int_ts1755007871551)
                );
                assign inj_data_out_1755007871551_969[i*4 +: 4] = temp_int_ts1755007871551[3:0];
            end
            // END: ModuleHierarchy_High_ts1755007871552

            mod_module_attrs mod_module_attrs_inst_1755007871549_4084 (
                .o_out(inj_o_out_1755007871549_73),
                .i_in(inj_i_in_1755007871549_563)
            );
            // BEGIN: net_var_conn_child_ts1755007871548
            assign inj_out_wire_1755007871548_204 = inj_data_ref_in_1755007871546_494;
            // END: net_var_conn_child_ts1755007871548

            mod_split_multiple_vars mod_split_multiple_vars_inst_1755007871547_1331 (
                .out_mv_c(inj_out_mv_c_1755007871547_949),
                .clk(clk),
                .data_in(split_case_var_ts1755007871545),
                .reset(reset),
                .out_mv_a(inj_out_mv_a_1755007871547_176),
                .out_mv_b(inj_out_mv_b_1755007871547_737)
            );
        always_comb begin
            var_m10_ts1755007871546 = inj_data_in_1755007871544_41;
            inj_out_val_m10_1755007871546_405 = inj_condition_m10_1755007871546_330 ? var_m10_ts1755007871546 : var_m10_ts1755007871546;
            var_m10_ts1755007871546++;
        end
        // END: unsupported_cond_expr_ts1755007871546

        // BEGIN: ansi_directions_ts1755007871546
        logic internal_data = 1'b0;
        assign inj_data_inout_1755007871546_886 = internal_data;
        always_comb begin
            inj_data_ref_out_1755007871546_964 = inj_data_ref_in_1755007871546_494;
            internal_data = inj_data_inout_1755007871546_886;
            inj_status_out_1755007871546_490 = internal_data | inj_control_in_1755007871546_44;
        end
        // END: ansi_directions_ts1755007871546

        Comb_Case Comb_Case_inst_1755007871545_3372 (
            .in0(inj_in0_1755007871545_19),
            .in1(inj_in1_1755007871545_240),
            .in2(inj_in2_1755007871545_6),
            .in3(inj_in3_1755007871545_289),
            .sel(inj_sel_1755007871545_224),
            .mux_out(inj_mux_out_1755007871545_164)
        );
        variable_sel_mux variable_sel_mux_inst_1755007871545_8945 (
            .out(inj_out_1755007871545_355),
            .in(split_case_var_ts1755007871545),
            .index(inj_index_1755007871545_985)
        );
    always_comb begin
        split_case_var_ts1755007871545 = 8'hFF;
        other_case_var_ts1755007871545 = 8'hAA;
        case (inj_sel_1755007871545_190)
            2'b00: begin
                split_case_var_ts1755007871545 = inj_data_in_1755007871544_41 + 5;
                other_case_var_ts1755007871545 = inj_data_in_1755007871544_41 + 6;
            end
            2'b01: begin
                split_case_var_ts1755007871545 = inj_data_in_1755007871544_41 - 5;
                other_case_var_ts1755007871545 = inj_data_in_1755007871544_41 - 6;
            end
            default: begin
                split_case_var_ts1755007871545 = inj_data_in_1755007871544_41;
                other_case_var_ts1755007871545 = inj_data_in_1755007871544_41;
            end
        endcase
        inj_out_case_a_1755007871544_252 = split_case_var_ts1755007871545;
        inj_out_case_b_1755007871544_628 = other_case_var_ts1755007871545;
    end
    // END: mod_split_case_ts1755007871545
endmodule

