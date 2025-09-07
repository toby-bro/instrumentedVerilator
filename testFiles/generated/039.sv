module CombinationalLogic (
    input logic enable,
    input logic [3:0] val_a,
    input logic [3:0] val_b,
    output logic [3:0] result
);
    always_comb begin
        if (enable) begin
            result = val_a + val_b;
        end else begin
            result = 4'h0;
        end
    end
endmodule

module LintAsyncFovIssue (
    input logic clk,
    input logic in_h,
    input logic rst_n,
    output logic out_i
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            out_i <= 1'b0;
        end else begin
            out_i <= in_h & out_i;
        end
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

module Module_ConfigKeywords (
    input bit cfg_in,
    output bit cfg_out
);
    assign cfg_out = cfg_in;
endmodule

module SimpleAssign (
    input logic [9:0] val_in,
    output logic [9:0] val_out
);
    assign val_out = val_in;
endmodule

module attributes_test (
    input logic i_attr_in,
    output logic o_attr_out
);
    (* synthesis_preserve *) logic internal_signal;
    always_comb begin : my_combinational_block
        internal_signal = i_attr_in ? 1'b1 : 1'b0;
        o_attr_out      = internal_signal;
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

module mismatched_width_unhandled (
    input logic [7:0] in,
    output logic [3:0] out
);
    assign out = in;
endmodule

module mod_unused_ports (
    input wire unused_in,
    output logic unused_out
);
    assign unused_out = unused_in;
endmodule

module multi_port_decl_module (
    input logic [3:0] p_a,
    input logic [3:0] p_b,
    input logic single_in,
    output logic single_out
);
    always_comb begin
        single_out = single_in;
    end
endmodule

module param_local_port #(
    parameter int P_PORT_VAL = 25
) (
    input logic i_reset,
    output logic [7:0] o_sum
);
    localparam int LP_BODY_VAL = 125;
    localparam int LP_CALCULATED = P_PORT_VAL + LP_BODY_VAL;
    always_comb begin
        if (i_reset) begin
            o_sum = 0;
        end else begin
            o_sum = LP_CALCULATED;
        end
    end
endmodule

module sequential_register (
    input logic clk,
    input logic data_in,
    input logic enable_in,
    input logic reset_n,
    output logic data_out
);
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            data_out <= 1'b0; 
        end else if (enable_in) begin
            data_out <= data_in; 
        end
    end
endmodule

module split_input_only_var (
    input logic clk_k,
    input logic control_signal_k,
    input logic [7:0] data_in_k,
    output logic [7:0] data_out_k
);
    always @(posedge clk_k) begin
        if (control_signal_k) begin
            data_out_k <= data_in_k;
        end
    end
endmodule

module snippet #(
    parameter int SEL_PARAM = 5
) (
    input wire clk,
    input logic [3:0] inj_a_1755007763932_226,
    input logic [3:0] inj_b_1755007763932_466,
    input bit [7:0] inj_data1_1755007763964_378,
    input bit [7:0] inj_data2_1755007763964_673,
    input logic [31:0] inj_data_in_1755007763995_437,
    input wire [3:0] inj_dffcl_ctrl_mode_1755007764027_614,
    input wire [15:0] inj_dffcl_data_in1_1755007764027_532,
    input wire [15:0] inj_dffcl_data_in2_1755007764027_996,
    input logic inj_in2_1755007763932_126,
    input logic [7:0] inj_in_1755007763932_307,
    input logic [7:0] inj_in_b_j_1755007763992_144,
    input logic [15:0] inj_in_data_1755007763938_72,
    input wire [7:0] inj_in_data_1755007763960_416,
    input wire [2:0] inj_in_index_1755007763980_416,
    input bit [3:0] inj_in_mask_z_1755007763957_449,
    input wire [1:0] inj_in_part_lsb_1755007763980_403,
    input bit inj_sel_1755007763964_846,
    input int inj_sel_in_1755007763934_428,
    input logic [4:0] inj_start_bit_1755007763995_870,
    input logic inj_sub_in_1755007763932_547,
    input logic [9:0] inj_val_in_1755007763947_403,
    input wire reset,
    output logic inj_bit_out_1755007763995_443,
    output logic [7:0] inj_byte_out_1755007763995_386,
    output bit inj_cfg_out_1755007764019_921,
    output bit inj_crypto_active_1755007763976_585,
    output logic [7:0] inj_data_out_1755007763934_464,
    output logic [3:0] inj_data_out_1755007763985_536,
    output logic inj_data_out_1755007764060_726,
    output logic [7:0] inj_data_out_k_1755007763953_965,
    output logic [15:0] inj_dffcl_data_out_1755007764027_102,
    output logic inj_eq_1755007763973_287,
    output logic [4:0] inj_internal_out_1755007763935_212,
    output logic inj_o_attr_out_1755007763966_211,
    output logic inj_o_done_ni_1755007763940_801,
    output logic [7:0] inj_o_sum_1755007764039_446,
    output logic [7:0] inj_out1_a_1755007763933_465,
    output logic [3:0] inj_out_1755007763932_272,
    output logic inj_out_1755007763932_436,
    output logic [7:0] inj_out_1755007763932_753,
    output logic [7:0] inj_out_1755007763942_27,
    output logic [15:0] inj_out_1755007763962_804,
    output logic [7:0] inj_out_1755007763998_131,
    output bit inj_out_1755007764003_857,
    output logic inj_out_bit_select_1755007763980_397,
    output logic [1:0] inj_out_bits_1755007763933_248,
    output logic [7:0] inj_out_bitwise_ops_1755007763980_399,
    output wire [7:0] inj_out_data_1755007763960_238,
    output logic [7:0] inj_out_field_a_1755007763938_368,
    output logic [7:0] inj_out_field_a_1755007764050_616,
    output logic [7:0] inj_out_field_b_1755007763938_331,
    output logic [7:0] inj_out_field_b_1755007764050_769,
    output logic inj_out_i_1755007763937_344,
    output logic inj_out_i_1755007763988_472,
    output bit [1:0] inj_out_match_type_z_1755007763957_426,
    output logic inj_out_md_1755007763933_299,
    output logic [3:0] inj_out_part_select_1755007763980_348,
    output bit inj_out_tc_1755007764090_25,
    output logic [7:0] inj_out_vector_assign_1755007763980_991,
    output logic [7:0] inj_out_x_j_1755007763992_581,
    output logic [7:0] inj_out_y_j_1755007763992_508,
    output bit [7:0] inj_result1_1755007763964_507,
    output bit [7:0] inj_result2_1755007763964_298,
    output logic [3:0] inj_result_1755007764070_589,
    output logic [3:0] inj_result_1755007764080_459,
    output logic inj_single_out_1755007764011_508,
    output logic inj_sub_out_1755007763932_710,
    output logic inj_sub_out_1755007763950_616,
    output logic [3:0] inj_sum_1755007763932_291,
    output logic [3:0] inj_test_case_result_1755007763943_54,
    output logic [3:0] inj_test_case_result_1755007763968_378,
    output logic inj_unused_out_1755007763971_76,
    output logic [9:0] inj_val_out_1755007763947_941
);
    // BEGIN: sub_module_ts1755007763932
    // BEGIN: simple_and_gate_ts1755007763932
    // BEGIN: CombinationalLogicImplicit_ts1755007763932
    // BEGIN: simple_assign_ts1755007763932
    // BEGIN: ModuleDefinition_ts1755007763933
    // BEGIN: split_basic_blocking_ts1755007763933
    // BEGIN: ModuleHierarchy_Low_ts1755007763935
    ModuleBasic m1 (
        .a     (1'b1),
        .b     (inj_sel_in_1755007763934_428),
        .out_a (),
        .out_b ( )
    );
    if (SEL_PARAM > 5) begin : gen_high
        int high_data_ts1755007763934;
        ModuleBasic m_high (
            .a     (1'b0),
            .b     (SEL_PARAM),
            .out_a (),
            .out_b (high_data_ts1755007763934)
        );
    end else begin : gen_low
        int low_data_ts1755007763934;
        ModuleBasic m_low (
            .a     (1'b0),
            .b     (SEL_PARAM),
            .out_a (),
            .out_b (low_data_ts1755007763934)
        );
    end
    for (genvar i = 0; i < 2; ++i) begin : gen_loop
        logic [1:0] sub_in_ts1755007763934;
        assign sub_in_ts1755007763934 = inj_a_1755007763932_226[i*2 +: 2];
        int temp_int_ts1755007763934;
            // BEGIN: simple_comb_ts1755007763960
            wire [7:0] intermediate_a_ts1755007763960;
            wire [7:0] intermediate_b_ts1755007763960;
            wire [7:0] intermediate_c_ts1755007763960;
                // BEGIN: sequential_logic_ts1755007763985
                ;
                logic [3:0] internal_reg_ts1755007763985;
                    // BEGIN: TopConfigExample_ts1755007764090
                    Module_ConfigKeywords i_cfg (.cfg_in(inj_sel_1755007763964_846), .cfg_out(inj_out_tc_1755007764090_25));
                    // END: TopConfigExample_ts1755007764090

                    // BEGIN: CombinationalLogic_ts1755007764080
                    always_comb begin
                        if (inj_in2_1755007763932_126) begin
                            inj_result_1755007764080_459 = inj_b_1755007763932_466 + internal_reg_ts1755007763985;
                        end else begin
                            inj_result_1755007764080_459 = 4'h0;
                        end
                    end
                    // END: CombinationalLogic_ts1755007764080

                    CombinationalLogic CombinationalLogic_inst_1755007764070_2649 (
                        .result(inj_result_1755007764070_589),
                        .enable(inj_in2_1755007763932_126),
                        .val_a(inj_b_1755007763932_466),
                        .val_b(inj_a_1755007763932_226)
                    );
                    sequential_register sequential_register_inst_1755007764060_9005 (
                        .enable_in(inj_sub_in_1755007763932_547),
                        .reset_n(reset),
                        .data_out(inj_data_out_1755007764060_726),
                        .clk(clk),
                        .data_in(inj_in2_1755007763932_126)
                    );
                    // BEGIN: StructExample_ts1755007764051
                    typedef struct packed {
                        logic [7:0] field_a_ts1755007764050;
                        logic [7:0] field_b_ts1755007764050;
                    } example_struct_t;
                    example_struct_t my_struct;
                    always_comb begin
                        my_struct     = inj_in_data_1755007763938_72;
                        inj_out_field_a_1755007764050_616   = my_struct.field_a_ts1755007764050;
                        inj_out_field_b_1755007764050_769   = my_struct.field_b_ts1755007764050;
                    end
                    // END: StructExample_ts1755007764051

                    param_local_port param_local_port_inst_1755007764039_4660 (
                        .i_reset(reset),
                        .o_sum(inj_o_sum_1755007764039_446)
                    );
                    // BEGIN: deep_ff_control_logic_ts1755007764029
                    always_ff @(posedge clk or negedge reset) begin
                    if (!reset) begin
                        inj_dffcl_data_out_1755007764027_102 <= 16'h0000;
                    end else begin
                        case (inj_dffcl_ctrl_mode_1755007764027_614)
                            4'd0: inj_dffcl_data_out_1755007764027_102 <= inj_dffcl_data_in1_1755007764027_532 + inj_dffcl_data_in2_1755007764027_996;
                            4'd1: begin
                                if (inj_dffcl_data_in1_1755007764027_532 > inj_dffcl_data_in2_1755007764027_996) begin
                                    case (inj_dffcl_ctrl_mode_1755007764027_614[1:0])
                                        2'b00: inj_dffcl_data_out_1755007764027_102 <= inj_dffcl_data_in1_1755007764027_532 - inj_dffcl_data_in2_1755007764027_996;
                                        2'b01: inj_dffcl_data_out_1755007764027_102 <= inj_dffcl_data_in1_1755007764027_532 & inj_dffcl_data_in2_1755007764027_996;
                                        default: inj_dffcl_data_out_1755007764027_102 <= inj_dffcl_data_in1_1755007764027_532 | inj_dffcl_data_in2_1755007764027_996;
                                    endcase
                                end else begin
                                    case (inj_dffcl_ctrl_mode_1755007764027_614[1:0])
                                        2'b00: inj_dffcl_data_out_1755007764027_102 <= inj_dffcl_data_in2_1755007764027_996 - inj_dffcl_data_in1_1755007764027_532;
                                        2'b01: inj_dffcl_data_out_1755007764027_102 <= inj_dffcl_data_in1_1755007764027_532 ^ inj_dffcl_data_in2_1755007764027_996;
                                        default: inj_dffcl_data_out_1755007764027_102 <= ~inj_dffcl_data_in1_1755007764027_532;
                                    endcase
                                end
                            end
                            4'd2: begin
                                casez (inj_dffcl_data_in1_1755007764027_532[15:13])
                                    3'b000: inj_dffcl_data_out_1755007764027_102 <= inj_dffcl_data_in2_1755007764027_996;
                                    3'b001: inj_dffcl_data_out_1755007764027_102 <= ~inj_dffcl_data_in2_1755007764027_996;
                                    3'b01?: begin
                                        if (inj_dffcl_data_in2_1755007764027_996[0]) inj_dffcl_data_out_1755007764027_102 <= inj_dffcl_data_in1_1755007764027_532 << 1;
                                        else inj_dffcl_data_out_1755007764027_102 <= inj_dffcl_data_in1_1755007764027_532 >> 1;
                                    end
                                    3'b1??: begin
                                        if (inj_dffcl_ctrl_mode_1755007764027_614[0]) inj_dffcl_data_out_1755007764027_102 <= inj_dffcl_data_in1_1755007764027_532 + 1;
                                        else inj_dffcl_data_out_1755007764027_102 <= inj_dffcl_data_in1_1755007764027_532 - 1;
                                    end
                                    default: inj_dffcl_data_out_1755007764027_102 <= 16'hAAAA;
                                endcase
                            end
                            default: begin
                                if (inj_dffcl_ctrl_mode_1755007764027_614[2]) inj_dffcl_data_out_1755007764027_102 <= inj_dffcl_data_in1_1755007764027_532;
                                else inj_dffcl_data_out_1755007764027_102 <= inj_dffcl_data_in2_1755007764027_996;
                            end
                        endcase
                    end
                    end
                    // END: deep_ff_control_logic_ts1755007764029

                    // BEGIN: Module_ConfigKeywords_ts1755007764019
                    assign inj_cfg_out_1755007764019_921 = inj_sel_1755007763964_846;
                    // END: Module_ConfigKeywords_ts1755007764019

                    multi_port_decl_module multi_port_decl_module_inst_1755007764011_3390 (
                        .single_in(inj_in2_1755007763932_126),
                        .single_out(inj_single_out_1755007764011_508),
                        .p_a(inj_b_1755007763932_466),
                        .p_b(inj_a_1755007763932_226)
                    );
                    // BEGIN: mod_default_disable_ts1755007764003
                    assign inj_out_1755007764003_857 = inj_sel_1755007763964_846;
                    // END: mod_default_disable_ts1755007764003

                    // BEGIN: simple_assign_ts1755007763998
                    assign inj_out_1755007763998_131 = inj_in_b_j_1755007763992_144;
                    // END: simple_assign_ts1755007763998

                    // BEGIN: ArrayIndexAndPartSelect_ts1755007763995
                    logic [31:0] internal_data = inj_data_in_1755007763995_437;
                    assign inj_bit_out_1755007763995_443 = internal_data[inj_sel_in_1755007763934_428];
                    assign inj_byte_out_1755007763995_386 = internal_data[inj_start_bit_1755007763995_870 +: 8];
                    // END: ArrayIndexAndPartSelect_ts1755007763995

                    // BEGIN: split_multiple_in_branch_ts1755007763992
                    always @(posedge clk) begin
                        if (inj_in2_1755007763932_126) begin
                            inj_out_x_j_1755007763992_581 <= inj_in_1755007763932_307 * 3;
                            inj_out_y_j_1755007763992_508 <= inj_in_b_j_1755007763992_144 + 1;
                        end else begin
                            inj_out_x_j_1755007763992_581 <= inj_in_1755007763932_307;
                            inj_out_y_j_1755007763992_508 <= inj_in_b_j_1755007763992_144;
                        end
                    end
                    // END: split_multiple_in_branch_ts1755007763992

                    LintAsyncFovIssue LintAsyncFovIssue_inst_1755007763988_9946 (
                        .clk(clk),
                        .in_h(inj_in2_1755007763932_126),
                        .rst_n(reset),
                        .out_i(inj_out_i_1755007763988_472)
                    );
                always_ff @(posedge clk or negedge reset) begin
                    if (!reset) begin
                        internal_reg_ts1755007763985 <= 4'h0;
                    end else begin
                        internal_reg_ts1755007763985 <= inj_b_1755007763932_466;
                    end
                end
                assign inj_data_out_1755007763985_536 = internal_reg_ts1755007763985;
                // END: sequential_logic_ts1755007763985

                // BEGIN: module_selection_ts1755007763981
                always_comb begin
                inj_out_vector_assign_1755007763980_991 = intermediate_b_ts1755007763960;
                inj_out_bit_select_1755007763980_397 = intermediate_b_ts1755007763960[inj_in_index_1755007763980_416];
                inj_out_part_select_1755007763980_348 = intermediate_b_ts1755007763960[inj_in_part_lsb_1755007763980_403 +: 4];
                inj_out_bitwise_ops_1755007763980_399 = intermediate_b_ts1755007763960 & {8{clk}};
                end
                // END: module_selection_ts1755007763981

                // BEGIN: PragmaProtectKeyBlock_ts1755007763976
            `ifdef SLANG_PRAGMA
            `protect key
            `endif
            `ifdef SLANG_PRAGMA
            `protect block
            `endif
            assign inj_crypto_active_1755007763976_585 = inj_sel_1755007763964_846;
                // END: PragmaProtectKeyBlock_ts1755007763976

                // BEGIN: ModCompareVec_ts1755007763973
                assign inj_eq_1755007763973_287 = (inj_b_1755007763932_466 == inj_a_1755007763932_226);
                // END: ModCompareVec_ts1755007763973

                mod_unused_ports mod_unused_ports_inst_1755007763971_6451 (
                    .unused_in(clk),
                    .unused_out(inj_unused_out_1755007763971_76)
                );
                // BEGIN: PragmaSyntaxVariety_ts1755007763968
            `ifdef SLANG_PRAGMA
            `unknown_pragma_real 1.23;
            `endif
            `ifdef SLANG_PRAGMA
            `unknown_slang_pragma (arg1, arg2="value")
            `endif
            `ifdef SLANG_PRAGMA
            `protect (1 + 2)
            `endif
            `ifdef SLANG_PRAGMA
            `protect {3, 4}
            `endif
            `ifdef SLANG_PRAGMA
            `protect unknown_action (arg=1)
            `endif
            `ifdef SLANG_PRAGMA
            `protect encoding
            `endif
            `ifdef SLANG_PRAGMA
            `protect encoding (enctype="raw", "string_arg_only")
            `endif
            `ifdef SLANG_PRAGMA
            `protect encoding (enctype="raw", unknown_option=99)
            `endif
            `ifdef SLANG_PRAGMA
            `protect encoding (bytes=-10)
            `endif
            `ifdef SLANG_PRAGMA
            `protect license (match="not_an_integer")
            `endif
            `ifdef SLANG_PRAGMA
            `protect license (match=42.5)
            `endif
            `ifdef SLANG_PRAGMA
            `protect viewport (obj="a", acc="b", extra=1)
            `endif
            `ifdef SLANG_PRAGMA
            `protect begin (arg_present)
            `endif
            `ifdef SLANG_PRAGMA
            `protect license ("license_string_only")
            `endif
            `ifdef SLANG_PRAGMA
            `protect license (library=my_library_ident)
            `endif
            `ifdef SLANG_PRAGMA
            `protect viewport (obj="a")
            `endif
            `ifdef SLANG_PRAGMA
            `protect viewport (obj="a", acc="b", c=3)
            `endif
            `ifdef SLANG_PRAGMA
            `protect viewport (obj="a", "access_string")
            `endif
            `ifdef SLANG_PRAGMA
            `protect viewport ("object_string", acc="b")
            `endif
            `ifdef SLANG_PRAGMA
            `protect viewport (object="a", access=123)
            `endif
            `ifdef SLANG_PRAGMA
            `protect viewport (object=123, access="b")
            `endif
            `ifdef SLANG_PRAGMA
            `protect viewport (not_object="a", access="b")
            `endif
            `ifdef SLANG_PRAGMA
            `protect viewport (object="a", not_access="b")
            `endif
            `ifdef SLANG_PRAGMA
            `diagnostic (1 + 2)
            `endif
            `ifdef SLANG_PRAGMA
            `diagnostic unknown_action_diag
            `endif
            `ifdef SLANG_PRAGMA
            `diagnostic level=warn
            `endif
            `ifdef SLANG_PRAGMA
            `diagnostic ignore (value=(1+2))
            `endif
            `ifdef SLANG_PRAGMA
            `diagnostic ignore (value=(value=1))
            `endif
            `ifdef SLANG_PRAGMA
            `diagnostic ignore (value=some_identifier)
            `endif
            `ifdef SLANG_PRAGMA
            `diagnostic warn (value=12345)
            `endif
            `ifdef SLANG_PRAGMA
            `diagnostic ignore simple_identifier_arg
            `endif
            `ifdef SLANG_PRAGMA
            `protect "simple_string_argument"
            `endif
            `ifdef SLANG_PRAGMA
            `diagnostic ignore "just_a_string_diag_code"
            `endif
            assign inj_test_case_result_1755007763968_378 = (sub_in_ts1755007763934 == 2'b01) ? 4'h5 : 4'hA;
                // END: PragmaSyntaxVariety_ts1755007763968

                attributes_test attributes_test_inst_1755007763966_3146 (
                    .i_attr_in(inj_sub_in_1755007763932_547),
                    .o_attr_out(inj_o_attr_out_1755007763966_211)
                );
                comb_conditional comb_conditional_inst_1755007763964_5888 (
                    .result2(inj_result2_1755007763964_298),
                    .data1(inj_data1_1755007763964_378),
                    .data2(inj_data2_1755007763964_673),
                    .sel(inj_sel_1755007763964_846),
                    .result1(inj_result1_1755007763964_507)
                );
                // BEGIN: always_comb_assign_ts1755007763962
                always_comb begin
                    inj_out_1755007763962_804 = inj_in_data_1755007763938_72;
                end
                // END: always_comb_assign_ts1755007763962

            assign intermediate_a_ts1755007763960 = inj_in_data_1755007763960_416 + 8'd1;
            assign intermediate_b_ts1755007763960 = intermediate_a_ts1755007763960 << 1;
            assign intermediate_c_ts1755007763960 = intermediate_a_ts1755007763960 >> 1;
            assign inj_out_data_1755007763960_238 = intermediate_b_ts1755007763960 | intermediate_c_ts1755007763960;
            // END: simple_comb_ts1755007763960

            // BEGIN: mod_casez_wildcard_ts1755007763958
        always_comb begin
            casez (inj_in_mask_z_1755007763957_449)
                4'b10?0: begin
                    inj_out_match_type_z_1755007763957_426 = 2'b00;
                end
                4'b011?: begin
                    inj_out_match_type_z_1755007763957_426 = 2'b01;
                end
                default: begin
                    inj_out_match_type_z_1755007763957_426 = 2'b11;
                end
            endcase
        end
            // END: mod_casez_wildcard_ts1755007763958

            split_input_only_var split_input_only_var_inst_1755007763953_3452 (
                .data_in_k(inj_in_1755007763932_307),
                .data_out_k(inj_data_out_k_1755007763953_965),
                .clk_k(clk),
                .control_signal_k(inj_sub_in_1755007763932_547)
            );
            // BEGIN: sub_module_ts1755007763950
            assign inj_sub_out_1755007763950_616 = !inj_sub_in_1755007763932_547;
            // END: sub_module_ts1755007763950

            SimpleAssign SimpleAssign_inst_1755007763947_3381 (
                .val_in(inj_val_in_1755007763947_403),
                .val_out(inj_val_out_1755007763947_941)
            );
            // BEGIN: PragmaSyntaxVariety_ts1755007763944
        `ifdef SLANG_PRAGMA
        `unknown_pragma_real 1.23;
        `endif
        `ifdef SLANG_PRAGMA
        `unknown_slang_pragma (arg1, arg2="value")
        `endif
        `ifdef SLANG_PRAGMA
        `protect (1 + 2)
        `endif
        `ifdef SLANG_PRAGMA
        `protect {3, 4}
        `endif
        `ifdef SLANG_PRAGMA
        `protect unknown_action (arg=1)
        `endif
        `ifdef SLANG_PRAGMA
        `protect encoding
        `endif
        `ifdef SLANG_PRAGMA
        `protect encoding (enctype="raw", "string_arg_only")
        `endif
        `ifdef SLANG_PRAGMA
        `protect encoding (enctype="raw", unknown_option=99)
        `endif
        `ifdef SLANG_PRAGMA
        `protect encoding (bytes=-10)
        `endif
        `ifdef SLANG_PRAGMA
        `protect license (match="not_an_integer")
        `endif
        `ifdef SLANG_PRAGMA
        `protect license (match=42.5)
        `endif
        `ifdef SLANG_PRAGMA
        `protect viewport (obj="a", acc="b", extra=1)
        `endif
        `ifdef SLANG_PRAGMA
        `protect begin (arg_present)
        `endif
        `ifdef SLANG_PRAGMA
        `protect license ("license_string_only")
        `endif
        `ifdef SLANG_PRAGMA
        `protect license (library=my_library_ident)
        `endif
        `ifdef SLANG_PRAGMA
        `protect viewport (obj="a")
        `endif
        `ifdef SLANG_PRAGMA
        `protect viewport (obj="a", acc="b", c=3)
        `endif
        `ifdef SLANG_PRAGMA
        `protect viewport (obj="a", "access_string")
        `endif
        `ifdef SLANG_PRAGMA
        `protect viewport ("object_string", acc="b")
        `endif
        `ifdef SLANG_PRAGMA
        `protect viewport (object="a", access=123)
        `endif
        `ifdef SLANG_PRAGMA
        `protect viewport (object=123, access="b")
        `endif
        `ifdef SLANG_PRAGMA
        `protect viewport (not_object="a", access="b")
        `endif
        `ifdef SLANG_PRAGMA
        `protect viewport (object="a", not_access="b")
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic (1 + 2)
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic unknown_action_diag
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic level=warn
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic ignore (value=(1+2))
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic ignore (value=(value=1))
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic ignore (value=some_identifier)
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic warn (value=12345)
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic ignore simple_identifier_arg
        `endif
        `ifdef SLANG_PRAGMA
        `protect "simple_string_argument"
        `endif
        `ifdef SLANG_PRAGMA
        `diagnostic ignore "just_a_string_diag_code"
        `endif
        assign inj_test_case_result_1755007763943_54 = (sub_in_ts1755007763934 == 2'b01) ? 4'h5 : 4'hA;
            // END: PragmaSyntaxVariety_ts1755007763944

            // BEGIN: simple_assign_ts1755007763942
            assign inj_out_1755007763942_27 = inj_in_1755007763932_307;
            // END: simple_assign_ts1755007763942

            // BEGIN: mod_no_inline_module_ts1755007763940
            logic r_toggle = 1'b0;
            always_ff @(posedge clk) begin
                r_toggle <= ~r_toggle;
            end
            assign inj_o_done_ni_1755007763940_801 = r_toggle;
            // END: mod_no_inline_module_ts1755007763940

            // BEGIN: StructExample_ts1755007763938
            typedef struct packed {
                logic [7:0] field_a_ts1755007763938;
                logic [7:0] field_b_ts1755007763938;
            } example_struct_t;
            example_struct_t my_struct;
            always_comb begin
                my_struct     = inj_in_data_1755007763938_72;
                inj_out_field_a_1755007763938_368   = my_struct.field_a_ts1755007763938;
                inj_out_field_b_1755007763938_331   = my_struct.field_b_ts1755007763938;
            end
            // END: StructExample_ts1755007763938

            LintAsyncFovIssue LintAsyncFovIssue_inst_1755007763937_3799 (
                .clk(clk),
                .in_h(inj_sub_in_1755007763932_547),
                .rst_n(reset),
                .out_i(inj_out_i_1755007763937_344)
            );
            // BEGIN: case_priority_casex_complex_mod_ts1755007763936
            always @* begin
                priority casex ({sub_in_ts1755007763934, inj_a_1755007763932_226[1:0]})
                    4'b1???: inj_internal_out_1755007763935_212 = 24;
                    4'b?1??: inj_internal_out_1755007763935_212 = 25;  
                    4'b??1?: inj_internal_out_1755007763935_212 = 26;  
                    4'b???1: inj_internal_out_1755007763935_212 = 27;  
                    4'b0000: inj_internal_out_1755007763935_212 = 28;  
                    default: inj_internal_out_1755007763935_212 = 29;
                endcase
            end
            // END: case_priority_casex_complex_mod_ts1755007763936

        ModuleBasic m_inst (
            .a      (1'b0),
            .b      (int'(sub_in_ts1755007763934)),
            .out_a  (),
            .out_b  (temp_int_ts1755007763934)
        );
        assign inj_data_out_1755007763934_464[i*4 +: 4] = temp_int_ts1755007763934[3:0];
    end
    // END: ModuleHierarchy_Low_ts1755007763935

    cast_select_demo cast_select_demo_inst_1755007763933_1050 (
        .in_data(inj_in_1755007763932_307),
        .out_bits(inj_out_bits_1755007763933_248)
    );
    always @(*) begin
        inj_out1_a_1755007763933_465 = inj_in_1755007763932_307;
    end
    // END: split_basic_blocking_ts1755007763933

    assign inj_out_md_1755007763933_299 = clk;
    // END: ModuleDefinition_ts1755007763933

    mismatched_width_unhandled mismatched_width_unhandled_inst_1755007763932_9850 (
        .in(inj_in_1755007763932_307),
        .out(inj_out_1755007763932_272)
    );
    assign inj_out_1755007763932_753 = inj_in_1755007763932_307;
    // END: simple_assign_ts1755007763932

    always @* begin
        inj_sum_1755007763932_291 = inj_a_1755007763932_226 + inj_b_1755007763932_466;
    end
    // END: CombinationalLogicImplicit_ts1755007763932

    assign inj_out_1755007763932_436 = inj_sub_in_1755007763932_547 & inj_in2_1755007763932_126;
    // END: simple_and_gate_ts1755007763932

    assign inj_sub_out_1755007763932_710 = !inj_sub_in_1755007763932_547;
    // END: sub_module_ts1755007763932
endmodule

