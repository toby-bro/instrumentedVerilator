interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
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

module ModuleDefinition (
    input wire in_md,
    output logic out_md
);
    assign out_md = in_md;
endmodule

module PragmaProtectOptions (
    input int config_data_in,
    output int config_data_out
);
`ifdef SLANG_PRAGMA
`protect encoding (enctype="base64", line_length=76, bytes=1024)
`endif
`ifdef SLANG_PRAGMA
`protect license (library="my_project_lib", entry="start_feature_A", match=42, feature="feature_set_B", exit="end_feature_A")
`endif
`ifdef SLANG_PRAGMA
`protect reset
`endif
`ifdef SLANG_PRAGMA
`protect viewport (object="design.module_a.instance_b.register_c", access="read-only")
`endif
assign config_data_out = config_data_in + 1;
endmodule

module PragmaResetDirectives (
    input bit reset_request,
    output bit system_status_clear
);
`ifdef SLANG_PRAGMA
`reset protect diagnostic
`endif
assign system_status_clear = reset_request;
endmodule

module mod_if_elseif_chained (
    input bit [7:0] in_value,
    output bit [2:0] out_category
);
always_comb begin
    if (in_value < 10) begin
        out_category = 3'd0;
    end else if (in_value < 50) begin
        out_category = 3'd1;
    end else if (in_value < 100) begin
        out_category = 3'd2;
    end else begin
        out_category = 3'd3;
    end
end
endmodule

module mod_named_begin (
    input int data_in,
    output int data_out
);
    always_comb begin : my_named_block
        data_out = data_in;
    end
endmodule

module module_assignments_in_loops (
    input logic [2:0] in_shift,
    input logic [7:0] in_val,
    output logic [3:0] out_part,
    output logic [7:0] out_reg
);
    localparam int PART_START = 4;
    localparam int PART_WIDTH = 4;
    logic [7:0] reg_var;
    logic [3:0] part_var;
    always_comb begin
        reg_var  = in_val;
        part_var = 4'h0;
        for (int i = 0; i < 4; i++) begin
            reg_var  = reg_var + i;
            reg_var += (i * 2);
            reg_var <<= in_shift;
            reg_var[i % 8] = (reg_var[i % 8] == 1'b0);
            reg_var[PART_START +: PART_WIDTH] = i[3:0];
        end
        part_var = reg_var[7:4];
    end
    assign out_reg  = reg_var;
    assign out_part = part_var;
endmodule

module snippet #(
    parameter int SEL_PARAM = 5
) (
    input wire clk,
    input int inj_b_1755007859381_636,
    input logic [7:0] inj_b_1755007859382_294,
    input logic [7:0] inj_c_1755007859382_995,
    input logic [15:0] inj_dividend_mod_1755007859384_732,
    input logic [15:0] inj_in_1755007859383_733,
    input logic [3:0] inj_in_h_1755007859381_793,
    input logic [3:0] inj_in_l_1755007859381_682,
    input logic [2:0] inj_in_shift_1755007859397_913,
    input bit [7:0] inj_in_value_1755007859408_719,
    input logic [7:0] inj_in_wide_1755007859380_177,
    input logic [1:0] inj_large_data_in_1755007859386_239,
    input logic inj_nm_in_1755007859380_437,
    input wire reset,
    output logic inj_anded_1755007859382_412,
    output int inj_config_data_out_1755007859385_830,
    output logic [7:0] inj_data_out_1755007859388_160,
    output int inj_data_out_1755007859401_986,
    output logic inj_diff_1755007859382_594,
    output logic [7:0] inj_large_sum_out_1755007859386_836,
    output logic inj_nm_out_1755007859380_895,
    output logic inj_ored_1755007859382_787,
    output logic [7:0] inj_out1_a_1755007859380_526,
    output logic inj_out1_bind_def_1755007859404_807,
    output logic [7:0] inj_out_1755007859381_789,
    output logic [15:0] inj_out_1755007859383_512,
    output logic [7:0] inj_out_1755007859391_100,
    output logic inj_out_a_1755007859381_667,
    output logic inj_out_a_1755007859394_907,
    output int inj_out_b_1755007859381_110,
    output int inj_out_b_1755007859394_56,
    output bit [2:0] inj_out_category_1755007859408_294,
    output logic [15:0] inj_out_concat_1755007859412_672,
    output logic [3:0] inj_out_h_1755007859419_3,
    output logic [3:0] inj_out_l_1755007859419_910,
    output logic inj_out_md_1755007859380_36,
    output logic [3:0] inj_out_narrow_1755007859380_906,
    output logic [3:0] inj_out_part_1755007859397_162,
    output logic [7:0] inj_out_reg_1755007859397_992,
    output reg inj_out_res_1755007859410_265,
    output logic inj_out_valid_status_1755007859421_136,
    output logic [15:0] inj_quotient_1755007859384_947,
    output logic [7:0] inj_remainder_1755007859384_485,
    output logic inj_reset_1755007859416_68,
    output logic [7:0] inj_sum_1755007859382_242,
    output bit inj_system_status_clear_1755007859414_444,
    output logic inj_xored_1755007859382_250
);
    // BEGIN: nested_module_ts1755007859380
    // BEGIN: LintImplicitWidth_ts1755007859380
    // BEGIN: split_basic_blocking_ts1755007859380
    // BEGIN: coalesced_assign_ts1755007859381
    wire [7:0] temp_wire_ts1755007859381;
        // BEGIN: ModuleBasic_ts1755007859381
        parameter int P1  = 10;
        localparam int LP1 = 20;
        logic c_ts1755007859381;
        int   d_ts1755007859381;
        always_comb begin
            logic temp_v_ts1755007859381;
                // BEGIN: loop_unroll_limit_test_ts1755007859386
                logic [7:0] current_large_sum_ts1755007859386;
                    // BEGIN: ModuleHierarchy_Low_ts1755007859389
                    ModuleBasic m1 (
                        .a     (1'b1),
                        .b     (inj_b_1755007859381_636),
                        .out_a (),
                        .out_b ( )
                    );
                    if (SEL_PARAM > 5) begin : gen_high
                        int high_data_ts1755007859388;
                        ModuleBasic m_high (
                            .a     (1'b0),
                            .b     (SEL_PARAM),
                            .out_a (),
                            .out_b (high_data_ts1755007859388)
                        );
                    end else begin : gen_low
                        int low_data_ts1755007859388;
                        ModuleBasic m_low (
                            .a     (1'b0),
                            .b     (SEL_PARAM),
                            .out_a (),
                            .out_b (low_data_ts1755007859388)
                        );
                    end
                    for (genvar i = 0; i < 2; ++i) begin : gen_loop
                        logic [1:0] sub_in_ts1755007859388;
                        assign sub_in_ts1755007859388 = inj_in_h_1755007859381_793[i*2 +: 2];
                        int temp_int_ts1755007859388;
                            // BEGIN: ModuleBasic_ts1755007859394
                            parameter int P1  = 10;
                            localparam int LP1 = 20;
                            logic c_ts1755007859394;
                            int   d_ts1755007859394;
                            always_comb begin
                                logic temp_v_ts1755007859394;
                                    // BEGIN: cu_timeunit_mod_ts1755007859417
                                    logic internal_sig_ts1755007859417;
                                        // BEGIN: module_assign_blocking_ts1755007859421
                                        my_if vif_inst();
                                        always_comb begin
                                            vif_inst.data = current_large_sum_ts1755007859386;
                                            vif_inst.valid = 1'b1;
                                            vif_inst.ready = 1'b0;
                                            inj_out_valid_status_1755007859421_136 = vif_inst.valid;
                                        end
                                        // END: module_assign_blocking_ts1755007859421

                                        // BEGIN: concat_assign_ts1755007859419
                                        assign {inj_out_h_1755007859419_3, inj_out_l_1755007859419_910} = inj_in_wide_1755007859380_177;
                                        // END: concat_assign_ts1755007859419

                                    always_ff @(posedge clk) begin
                                        inj_reset_1755007859416_68 <= 1'b0;
                                        internal_sig_ts1755007859417 = clk;
                                    end
                                    // END: cu_timeunit_mod_ts1755007859417

                                    PragmaResetDirectives PragmaResetDirectives_inst_1755007859414_1850 (
                                        .system_status_clear(inj_system_status_clear_1755007859414_444),
                                        .reset_request(reset)
                                    );
                                    // BEGIN: ConcatVectorOps_ts1755007859412
                                    assign inj_out_concat_1755007859412_672 = {inj_in_h_1755007859381_793, inj_in_l_1755007859381_682, current_large_sum_ts1755007859386};
                                    // END: ConcatVectorOps_ts1755007859412

                                    // BEGIN: case_single_default_after_item_ts1755007859410
                                    always_comb begin
                                        inj_out_res_1755007859410_265 = 1'b0;
                                        case (sub_in_ts1755007859388)
                                            2'b01: inj_out_res_1755007859410_265 = 1'b1;
                                            default: inj_out_res_1755007859410_265 = 1'b0;
                                            2'b10: inj_out_res_1755007859410_265 = 1'b1;
                                        endcase
                                    end
                                    // END: case_single_default_after_item_ts1755007859410

                                    mod_if_elseif_chained mod_if_elseif_chained_inst_1755007859408_982 (
                                        .in_value(inj_in_value_1755007859408_719),
                                        .out_category(inj_out_category_1755007859408_294)
                                    );
                                    // BEGIN: mod_basic_bind_ts1755007859404
                                    assign inj_out1_bind_def_1755007859404_807 = ~inj_nm_in_1755007859380_437;
                                    // END: mod_basic_bind_ts1755007859404

                                    mod_named_begin mod_named_begin_inst_1755007859401_3228 (
                                        .data_in(d_ts1755007859394),
                                        .data_out(inj_data_out_1755007859401_986)
                                    );
                                    module_assignments_in_loops module_assignments_in_loops_inst_1755007859397_7463 (
                                        .in_val(inj_c_1755007859382_995),
                                        .out_part(inj_out_part_1755007859397_162),
                                        .out_reg(inj_out_reg_1755007859397_992),
                                        .in_shift(inj_in_shift_1755007859397_913)
                                    );
                                temp_v_ts1755007859394 = d_ts1755007859394;
                                c_ts1755007859394      = temp_v_ts1755007859394;
                            end
                            assign inj_out_a_1755007859394_907 = c_ts1755007859381;
                            assign d_ts1755007859394     = temp_int_ts1755007859388;
                            assign inj_out_b_1755007859394_56 = d_ts1755007859394 + P1 + LP1;
                            // END: ModuleBasic_ts1755007859394

                            // BEGIN: sub_inst_array_mod_ts1755007859391
                            assign inj_out_1755007859391_100 = inj_b_1755007859382_294;
                            // END: sub_inst_array_mod_ts1755007859391

                        ModuleBasic m_inst (
                            .a      (1'b0),
                            .b      (int'(sub_in_ts1755007859388)),
                            .out_a  (),
                            .out_b  (temp_int_ts1755007859388)
                        );
                        assign inj_data_out_1755007859388_160[i*4 +: 4] = temp_int_ts1755007859388[3:0];
                    end
                    // END: ModuleHierarchy_Low_ts1755007859389

                always_comb begin
                    current_large_sum_ts1755007859386 = 8'h00;
                    for (int m = 0; m < 40; m = m + 1) begin 
                        current_large_sum_ts1755007859386 = current_large_sum_ts1755007859386 + inj_large_data_in_1755007859386_239[0];
                        current_large_sum_ts1755007859386 = current_large_sum_ts1755007859386 + inj_large_data_in_1755007859386_239[1];
                        current_large_sum_ts1755007859386 = current_large_sum_ts1755007859386 + 1;
                    end
                    inj_large_sum_out_1755007859386_836 = current_large_sum_ts1755007859386;
                end
                // END: loop_unroll_limit_test_ts1755007859386

                PragmaProtectOptions PragmaProtectOptions_inst_1755007859385_8501 (
                    .config_data_in(d_ts1755007859381),
                    .config_data_out(inj_config_data_out_1755007859385_830)
                );
                // BEGIN: div_mod_ops_ts1755007859384
                assign inj_quotient_1755007859384_947 = (inj_c_1755007859382_995 == 0) ? 16'hFFFF : (inj_in_1755007859383_733 / inj_c_1755007859382_995); 
                assign inj_remainder_1755007859384_485 = (inj_b_1755007859382_294 == 0) ? 8'hFF : (inj_dividend_mod_1755007859384_732 % inj_b_1755007859382_294);
                // END: div_mod_ops_ts1755007859384

                // BEGIN: always_comb_assign_ts1755007859383
                always_comb begin
                    inj_out_1755007859383_512 = inj_in_1755007859383_733;
                end
                // END: always_comb_assign_ts1755007859383

                // BEGIN: more_ops_ts1755007859382
                assign inj_sum_1755007859382_242 = inj_in_wide_1755007859380_177 + inj_b_1755007859382_294;
                assign inj_diff_1755007859382_594 = inj_in_wide_1755007859380_177 > inj_c_1755007859382_995;
                assign inj_anded_1755007859382_412 = inj_in_wide_1755007859380_177 & inj_b_1755007859382_294;
                assign inj_ored_1755007859382_787 = inj_in_wide_1755007859380_177 | inj_c_1755007859382_995;
                assign inj_xored_1755007859382_250 = inj_in_wide_1755007859380_177 ^ inj_b_1755007859382_294;
                // END: more_ops_ts1755007859382

            temp_v_ts1755007859381 = d_ts1755007859381;
            c_ts1755007859381      = temp_v_ts1755007859381;
        end
        assign inj_out_a_1755007859381_667 = inj_nm_in_1755007859380_437;
        assign d_ts1755007859381     = inj_b_1755007859381_636;
        assign inj_out_b_1755007859381_110 = d_ts1755007859381 + P1 + LP1;
        // END: ModuleBasic_ts1755007859381

    assign temp_wire_ts1755007859381[7:4] = inj_in_h_1755007859381_793;
    assign temp_wire_ts1755007859381[3:0] = inj_in_l_1755007859381_682;
    assign inj_out_1755007859381_789 = temp_wire_ts1755007859381;
    // END: coalesced_assign_ts1755007859381

    always @(*) begin
        inj_out1_a_1755007859380_526 = inj_in_wide_1755007859380_177;
    end
    // END: split_basic_blocking_ts1755007859380

    assign inj_out_narrow_1755007859380_906 = inj_in_wide_1755007859380_177;
    // END: LintImplicitWidth_ts1755007859380

    assign inj_nm_out_1755007859380_895 = inj_nm_in_1755007859380_437;
    // END: nested_module_ts1755007859380

    ModuleDefinition ModuleDefinition_inst_1755007859380_2311 (
        .in_md(reset),
        .out_md(inj_out_md_1755007859380_36)
    );
endmodule

