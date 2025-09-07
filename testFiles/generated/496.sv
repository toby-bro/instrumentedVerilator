module LintUnusedSignal (
    input logic in_a,
    output logic out_b
);
    logic unused_w; 
    assign out_b = in_a;
endmodule

module ModRegister (
    input logic din,
    output logic dout
);
    always @* begin
        dout = din;
    end
endmodule

module Module_ConfigKeywords (
    input bit cfg_in,
    output bit cfg_out
);
    assign cfg_out = cfg_in;
endmodule

module SimpleLoopExample (
    input logic [7:0] in_vec,
    output logic [7:0] out_vec
);
    always_comb begin
        for (int i = 0; i < 8; i++) begin
            out_vec[i] = in_vec[7 - i];
        end
    end
endmodule

module basic_d_flipflop (
    input logic clk,
    input logic d,
    output logic q
);
    always_ff @(posedge clk) begin
        q <= d;
    end
endmodule

module case_default (
    input logic [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b01: out_res = 1'b1;
            2'b10: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
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

module macro_concat_user (
    input logic [3:0] concat_in,
    output logic [7:0] concat_out
);
    `define MAKE_NAME(a,b) a``b
    logic var_signal;
    always_comb begin
        `MAKE_NAME(var,_signal) = concat_in[0];
    end
    assign concat_out = {4'b0, concat_in[3:1], var_signal};
endmodule

module module_bitfield_concat (
    input logic [7:0] input_bf,
    input logic [3:0] input_bf_slice,
    output logic [7:0] output_bf,
    output logic [3:0] output_bf_slice
);
    logic [7:0] my_bitfield ;
    always_comb begin
        if (input_bf[7]) begin
            my_bitfield = input_bf;
        end else begin
            my_bitfield = {input_bf[0], input_bf[7:1]};
        end
        my_bitfield[3:0] = input_bf_slice;
    end
    assign output_bf = my_bitfield;
    assign output_bf_slice = my_bitfield[3:0];
endmodule

module module_in_program_ref (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module module_with_unconnected_drive (
    input logic in_data,
    output logic out_data_pull0,
    output logic out_data_pull1
);
    assign out_data_pull1 = in_data;
    assign out_data_pull0 = ~in_data;
endmodule

module multiplexer_2to1 (
    input logic data0,
    input logic data1,
    input logic sel,
    output logic result
);
    assign result = sel ? data1 : data0;
endmodule

module split_mixed_cond_seq (
    input logic clk_e,
    input logic condition_e,
    input logic [7:0] in_override_e,
    input logic [7:0] in_val_e,
    output logic [7:0] out_val_e,
    output logic status_e
);
    logic [7:0] temp_val_e;
    always @(posedge clk_e) begin
        temp_val_e <= in_val_e + 5;
        if (condition_e) begin
            out_val_e <= temp_val_e;
            status_e <= 1;
        end else begin
            out_val_e <= in_override_e;
            status_e <= 0;
        end
    end
endmodule

module virtual_interface_lookup_mod (
    input logic dummy_in,
    input logic [7:0] vif_data,
    input logic vif_valid,
    output logic dummy_out,
    output logic [7:0] out_data,
    output logic out_valid
);
    always_comb begin
        out_data  = vif_data;
        out_valid = vif_valid;
        dummy_out = dummy_in;
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_c_1755007919966_708,
    input logic [3:0] inj_concat_in_1755007919967_9,
    input logic [7:0] inj_d3_w_1755007920001_3,
    input logic [9:0] inj_data_in_pl_1755007919963_673,
    input logic inj_din_1755007919963_679,
    input wire inj_g_in_1755007919962_782,
    input bit [7:0] inj_in1_1755007919962_350,
    input logic inj_in1_1755007919966_275,
    input bit [7:0] inj_in2_1755007919962_107,
    input bit [3:0] inj_in_data_1755007919963_847,
    input logic [7:0] inj_in_override_e_1755007919963_174,
    input bit inj_in_tc_1755007919962_695,
    input wire [7:0] inj_in_val1_1755007919980_654,
    input wire [7:0] inj_in_val2_1755007919980_170,
    input int inj_in_val_1755007919962_2,
    input logic [1:0] inj_in_val_1755007919968_244,
    input logic [7:0] inj_in_val_e_1755007919963_841,
    input logic [15:0] inj_in_vector_1755007919963_285,
    input wire reset,
    output logic [7:0] inj_concat_out_1755007919967_346,
    output logic [4:0] inj_data_out_pl_1755007919963_263,
    output logic inj_dout_1755007919963_544,
    output logic inj_dummy_1755007919970_601,
    output logic inj_dummy_out_1755007919985_308,
    output wire inj_g_out_and_1755007919962_778,
    output wire inj_g_out_or_1755007919962_696,
    output logic inj_o_bind_status_1755007919975_538,
    output bit [7:0] inj_out1_1755007919962_254,
    output bit [7:0] inj_out2_1755007919962_511,
    output logic [7:0] inj_out_1755007919965_448,
    output logic inj_out_1755007919966_666,
    output logic inj_out_a_1755007919987_865,
    output logic inj_out_b_1755007919977_3,
    output int inj_out_b_1755007919987_299,
    output logic inj_out_b_1755007919990_734,
    output logic [1:0] inj_out_bits_1755007919964_691,
    output logic [7:0] inj_out_data_1755007919985_184,
    output logic inj_out_data_pull0_1755007919969_659,
    output logic inj_out_data_pull1_1755007919969_723,
    output logic inj_out_r_1755007919997_142,
    output reg inj_out_res_1755007919968_31,
    output bit [3:0] inj_out_result_1755007919963_825,
    output logic [7:0] inj_out_slice_1755007919963_621,
    output bit [3:0] inj_out_status_1755007919964_428,
    output bit inj_out_tc_1755007919962_405,
    output logic [7:0] inj_out_ternary_result_1755007919980_117,
    output logic [7:0] inj_out_v_1755007920004_588,
    output int inj_out_val_1755007919962_927,
    output logic [7:0] inj_out_val_e_1755007919963_536,
    output logic inj_out_valid_1755007919985_43,
    output logic [7:0] inj_out_vec_1755007919973_416,
    output logic [7:0] inj_out_w_1755007920001_397,
    output logic [7:0] inj_output_bf_1755007919969_508,
    output logic [3:0] inj_output_bf_slice_1755007919969_110,
    output logic inj_q_1755007919965_141,
    output logic inj_result_1755007919994_617,
    output logic [7:0] inj_result_and_1755007919966_948,
    output logic [7:0] inj_result_or_1755007919966_462,
    output logic [7:0] inj_result_xor_1755007919966_643,
    output logic inj_status_e_1755007919963_122,
    output logic inj_unused_out_1755007919982_853
);
    // BEGIN: comb_simple_ts1755007919962
    // BEGIN: TopConfigExample_ts1755007919962
    // BEGIN: Module_GatePrimitives_ts1755007919962
    // BEGIN: MiscExpressions_ValueRange_ts1755007919963
    // BEGIN: module_packed_logic_ts1755007919963
    logic [15:0] my_packed_logic_ts1755007919963 ;
        // BEGIN: ModuleBasic_ts1755007919988
        parameter int P1  = 10;
        localparam int LP1 = 20;
        logic c_ts1755007919987;
        int   d_ts1755007919987;
        always_comb begin
            logic temp_v_ts1755007919987;
                // BEGIN: LintUnusedSignal_ts1755007919990
                logic unused_w_ts1755007919990; 
                    // BEGIN: ModVectorAdd_ts1755007920004
                    assign inj_out_v_1755007920004_588 = inj_c_1755007919966_708 + 8'h01;
                    // END: ModVectorAdd_ts1755007920004

                    // BEGIN: split_case_ts1755007920001
                    always @(posedge clk) begin
                        case (inj_in_val_1755007919968_244)
                            2'b00: inj_out_w_1755007920001_397 <= inj_in_val_e_1755007919963_841;
                            2'b01: inj_out_w_1755007920001_397 <= inj_in_override_e_1755007919963_174;
                            2'b10: inj_out_w_1755007920001_397 <= inj_c_1755007919966_708;
                            default: inj_out_w_1755007920001_397 <= inj_d3_w_1755007920001_3;
                        endcase
                    end
                    // END: split_case_ts1755007920001

                    // BEGIN: LintSensitiveList_ts1755007919997
                    always_comb begin
                        inj_out_r_1755007919997_142 = unused_w_ts1755007919990 | inj_din_1755007919963_679;
                    end
                    // END: LintSensitiveList_ts1755007919997

                    multiplexer_2to1 multiplexer_2to1_inst_1755007919994_3119 (
                        .sel(inj_in1_1755007919966_275),
                        .result(inj_result_1755007919994_617),
                        .data0(unused_w_ts1755007919990),
                        .data1(c_ts1755007919987)
                    );
                assign inj_out_b_1755007919990_734 = temp_v_ts1755007919987;
                // END: LintUnusedSignal_ts1755007919990

            temp_v_ts1755007919987 = d_ts1755007919987;
            c_ts1755007919987      = temp_v_ts1755007919987;
        end
        assign inj_out_a_1755007919987_865 = inj_in1_1755007919966_275;
        assign d_ts1755007919987     = inj_in_val_1755007919962_2;
        assign inj_out_b_1755007919987_299 = d_ts1755007919987 + P1 + LP1;
        // END: ModuleBasic_ts1755007919988

        virtual_interface_lookup_mod virtual_interface_lookup_mod_inst_1755007919985_4443 (
            .dummy_out(inj_dummy_out_1755007919985_308),
            .out_data(inj_out_data_1755007919985_184),
            .out_valid(inj_out_valid_1755007919985_43),
            .dummy_in(inj_din_1755007919963_679),
            .vif_data(inj_in_override_e_1755007919963_174),
            .vif_valid(inj_in1_1755007919966_275)
        );
        // BEGIN: mod_unused_ports_ts1755007919982
        assign inj_unused_out_1755007919982_853 = reset;
        // END: mod_unused_ports_ts1755007919982

        // BEGIN: module_ternary_ts1755007919980
        always_comb begin
        inj_out_ternary_result_1755007919980_117 = reset ? inj_in_val1_1755007919980_654 : inj_in_val2_1755007919980_170;
        end
        // END: module_ternary_ts1755007919980

        LintUnusedSignal LintUnusedSignal_inst_1755007919977_5898 (
            .in_a(inj_din_1755007919963_679),
            .out_b(inj_out_b_1755007919977_3)
        );
        // BEGIN: module_to_bind_ts1755007919975
        always_comb inj_o_bind_status_1755007919975_538 = |inj_concat_in_1755007919967_9;
        // END: module_to_bind_ts1755007919975

        SimpleLoopExample SimpleLoopExample_inst_1755007919973_2559 (
            .in_vec(inj_in_override_e_1755007919963_174),
            .out_vec(inj_out_vec_1755007919973_416)
        );
        // BEGIN: mod_err_event_constant_ts1755007919970
        always @(posedge 1'b1) begin
            inj_dummy_1755007919970_601 = ~inj_dummy_1755007919970_601;
        end
        // END: mod_err_event_constant_ts1755007919970

        module_with_unconnected_drive module_with_unconnected_drive_inst_1755007919969_5955 (
            .in_data(inj_din_1755007919963_679),
            .out_data_pull0(inj_out_data_pull0_1755007919969_659),
            .out_data_pull1(inj_out_data_pull1_1755007919969_723)
        );
        module_bitfield_concat module_bitfield_concat_inst_1755007919969_3521 (
            .output_bf(inj_output_bf_1755007919969_508),
            .output_bf_slice(inj_output_bf_slice_1755007919969_110),
            .input_bf(inj_c_1755007919966_708),
            .input_bf_slice(inj_concat_in_1755007919967_9)
        );
        case_default case_default_inst_1755007919968_1610 (
            .in_val(inj_in_val_1755007919968_244),
            .out_res(inj_out_res_1755007919968_31)
        );
        macro_concat_user macro_concat_user_inst_1755007919967_8156 (
            .concat_out(inj_concat_out_1755007919967_346),
            .concat_in(inj_concat_in_1755007919967_9)
        );
        // BEGIN: BitwiseOperations_ts1755007919967
        assign inj_result_and_1755007919966_948 = inj_in_val_e_1755007919963_841 & inj_in_override_e_1755007919963_174;
        assign inj_result_or_1755007919966_462 = inj_in_val_e_1755007919963_841 | inj_c_1755007919966_708;
        assign inj_result_xor_1755007919966_643 = inj_in_override_e_1755007919963_174 ^ inj_c_1755007919966_708;
        // END: BitwiseOperations_ts1755007919967

        // BEGIN: simple_and_gate_ts1755007919966
        assign inj_out_1755007919966_666 = inj_in1_1755007919966_275 & inj_din_1755007919963_679;
        // END: simple_and_gate_ts1755007919966

        // BEGIN: sub_inst_array_mod_ts1755007919965
        assign inj_out_1755007919965_448 = inj_in_val_e_1755007919963_841;
        // END: sub_inst_array_mod_ts1755007919965

        basic_d_flipflop basic_d_flipflop_inst_1755007919965_4009 (
            .d(inj_din_1755007919963_679),
            .q(inj_q_1755007919965_141),
            .clk(clk)
        );
        cast_select_demo cast_select_demo_inst_1755007919964_2777 (
            .in_data(inj_in_override_e_1755007919963_174),
            .out_bits(inj_out_bits_1755007919964_691)
        );
        // BEGIN: mod_case_standard_ts1755007919964
    always_comb begin
        case (inj_in2_1755007919962_107)
            8'd0, 8'd1, 8'd2: begin
                inj_out_status_1755007919964_428 = 4'hA;
            end
            8'd3, 8'd4: begin
                inj_out_status_1755007919964_428 = 4'hB;
            end
            default: begin
                inj_out_status_1755007919964_428 = 4'hF;
            end
        endcase
    end
        // END: mod_case_standard_ts1755007919964

        // BEGIN: mod_if_else_simple_ts1755007919963
    always_comb begin
        if (inj_in_data_1755007919963_847 > 8) begin
            inj_out_result_1755007919963_825 = inj_in_data_1755007919963_847 + 1;
        end else begin
            inj_out_result_1755007919963_825 = inj_in_data_1755007919963_847 - 1;
        end
    end
        // END: mod_if_else_simple_ts1755007919963

        split_mixed_cond_seq split_mixed_cond_seq_inst_1755007919963_1138 (
            .status_e(inj_status_e_1755007919963_122),
            .clk_e(clk),
            .condition_e(inj_din_1755007919963_679),
            .in_override_e(inj_in_override_e_1755007919963_174),
            .in_val_e(inj_in_val_e_1755007919963_841),
            .out_val_e(inj_out_val_e_1755007919963_536)
        );
    always_comb begin
        my_packed_logic_ts1755007919963[9:0] = inj_data_in_pl_1755007919963_673;
        my_packed_logic_ts1755007919963[15:10] = 6'h3F;
        my_packed_logic_ts1755007919963[0] = inj_din_1755007919963_679;
    end
    assign inj_data_out_pl_1755007919963_263[4:1] = my_packed_logic_ts1755007919963[4:1];
    assign inj_data_out_pl_1755007919963_263[0] = my_packed_logic_ts1755007919963[1];
    // END: module_packed_logic_ts1755007919963

    ModRegister ModRegister_inst_1755007919963_3536 (
        .din(inj_din_1755007919963_679),
        .dout(inj_dout_1755007919963_544)
    );
    always_comb begin
        inj_out_slice_1755007919963_621 = inj_in_vector_1755007919963_285[7:0];
    end
    // END: MiscExpressions_ValueRange_ts1755007919963

    and a1 (inj_g_out_and_1755007919962_778, inj_g_in_1755007919962_782, inj_g_in_1755007919962_782);
    or  o1 (inj_g_out_or_1755007919962_696 , inj_g_in_1755007919962_782, inj_g_in_1755007919962_782);
    // END: Module_GatePrimitives_ts1755007919962

    Module_ConfigKeywords i_cfg (.cfg_in(inj_in_tc_1755007919962_695), .cfg_out(inj_out_tc_1755007919962_405));
    // END: TopConfigExample_ts1755007919962

    module_in_program_ref module_in_program_ref_inst_1755007919962_6162 (
        .out_val(inj_out_val_1755007919962_927),
        .in_val(inj_in_val_1755007919962_2)
    );
    always @* begin
        inj_out1_1755007919962_254 = inj_in1_1755007919962_350 & inj_in2_1755007919962_107;
        inj_out2_1755007919962_511 = inj_in1_1755007919962_350 | inj_in2_1755007919962_107;
    end
    // END: comb_simple_ts1755007919962
endmodule

