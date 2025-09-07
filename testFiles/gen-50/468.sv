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

module snippet #(
    parameter integer DATA_WIDTH = 8,
    parameter bit GEN = 1,
    parameter int SEL_PARAM = 5
) (
    input wire clk,
    input logic [3:0] inj_a_1755007910609_597,
    input logic [3:0] inj_b_1755007910609_69,
    input logic [7:0] inj_data_b_1755007910614_364,
    input wire [3:0] inj_dffcl_ctrl_mode_1755007910608_659,
    input wire [15:0] inj_dffcl_data_in1_1755007910608_27,
    input wire [15:0] inj_dffcl_data_in2_1755007910608_662,
    input wire [1:0] inj_in_const_index_1755007910617_480,
    input wire [7:0] inj_in_data_1755007910617_960,
    input wire [1:0] inj_in_index_1755007910617_290,
    input logic [2:0] inj_in_val_1755007910627_608,
    input logic inj_sel_1755007910619_459,
    input int inj_sel_in_1755007910613_593,
    input logic [7:0] inj_start_val_i_1755007910607_960,
    input logic [1:0] inj_test_case_mode_1755007910610_756,
    input wire reset,
    output logic [7:0] inj_data_out_1755007910613_899,
    output logic [15:0] inj_dffcl_data_out_1755007910608_793,
    output logic [4:0] inj_internal_out_1755007910616_975,
    output logic [7:0] inj_o_target_result_1755007910612_898,
    output logic [7:0] inj_out2_a_1755007910608_473,
    output logic [7:0] inj_out_array_sel_const_1755007910617_588,
    output logic [7:0] inj_out_array_sel_var_1755007910617_334,
    output logic inj_out_b_1755007910639_865,
    output reg inj_out_res_1755007910627_107,
    output int inj_out_val_1755007910619_540,
    output logic inj_out_wire_1755007910635_987,
    output wire [7:0] inj_param_out_1755007910624_27,
    output logic [7:0] inj_result1_1755007910614_340,
    output logic [7:0] inj_result2_1755007910614_144,
    output logic inj_sig_out_1755007910631_48,
    output logic [3:0] inj_sum_1755007910609_147,
    output logic [15:0] inj_sum_out_i_1755007910607_590,
    output logic [3:0] inj_test_case_result_1755007910610_87
);
    // BEGIN: split_for_loop_ts1755007910608
    // BEGIN: split_basic_nonblocking_ts1755007910608
    // BEGIN: deep_ff_control_logic_ts1755007910609
    // BEGIN: CombinationalLogicImplicit_ts1755007910610
    // BEGIN: PragmaSyntaxVariety_ts1755007910611
`ifdef SLANG_PRAGMA
`unknown_pragma_real 1.23;
    // BEGIN: ModuleHierarchy_Low_ts1755007910613
    ModuleBasic m1 (
        .a     (1'b1),
        .b     (inj_sel_in_1755007910613_593),
        .out_a (),
        .out_b ( )
    );
    if (SEL_PARAM > 5) begin : gen_high
        int high_data_ts1755007910613;
        ModuleBasic m_high (
            .a     (1'b0),
            .b     (SEL_PARAM),
            .out_a (),
            .out_b (high_data_ts1755007910613)
        );
    end else begin : gen_low
        int low_data_ts1755007910613;
        ModuleBasic m_low (
            .a     (1'b0),
            .b     (SEL_PARAM),
            .out_a (),
            .out_b (low_data_ts1755007910613)
        );
    end
    for (genvar i = 0; i < 2; ++i) begin : gen_loop
        logic [1:0] sub_in_ts1755007910613;
        assign sub_in_ts1755007910613 = inj_a_1755007910609_597[i*2 +: 2];
        int temp_int_ts1755007910613;
            // BEGIN: Mod_ArrayOps_ts1755007910618
            logic [7:0] my_array_ts1755007910618 [3:0];
                // BEGIN: LintUnusedSignal_ts1755007910640
                logic unused_w_ts1755007910639; 
                assign inj_out_b_1755007910639_865 = inj_sel_1755007910619_459;
                // END: LintUnusedSignal_ts1755007910640

                // BEGIN: net_var_conn_child_ts1755007910635
                assign inj_out_wire_1755007910635_987 = inj_sel_1755007910619_459;
                // END: net_var_conn_child_ts1755007910635

                // BEGIN: GenerateIfParam_ts1755007910631
                generate
                    if (GEN) begin : g_true
                        assign inj_sig_out_1755007910631_48 = inj_sel_1755007910619_459;
                    end
                    else begin : g_false
                        assign inj_sig_out_1755007910631_48 = ~inj_sel_1755007910619_459;
                    end
                endgenerate
                // END: GenerateIfParam_ts1755007910631

                // BEGIN: casez_xz_ts1755007910628
                always_comb begin
                    inj_out_res_1755007910627_107 = 1'b0;
                    casez (inj_in_val_1755007910627_608)
                        3'b1??: inj_out_res_1755007910627_107 = 1'b1;
                        3'b0z?: inj_out_res_1755007910627_107 = 1'b0;
                        default: inj_out_res_1755007910627_107 = 1'b1;
                    endcase
                end
                // END: casez_xz_ts1755007910628

                // BEGIN: module_with_params_ts1755007910624
                assign inj_param_out_1755007910624_27 = inj_in_data_1755007910617_960;
                // END: module_with_params_ts1755007910624

                // BEGIN: ConditionalOps_ts1755007910620
                assign inj_out_val_1755007910619_540 = inj_sel_1755007910619_459 ? inj_sel_in_1755007910613_593 : temp_int_ts1755007910613;
                // END: ConditionalOps_ts1755007910620

            always_comb begin
                my_array_ts1755007910618[0] = inj_in_data_1755007910617_960;
                my_array_ts1755007910618[1] = inj_in_data_1755007910617_960 + 8'd1;
                my_array_ts1755007910618[2] = inj_in_data_1755007910617_960 + 8'd2;
                my_array_ts1755007910618[3] = inj_in_data_1755007910617_960 + 8'd3;
                inj_out_array_sel_var_1755007910617_334 = my_array_ts1755007910618[inj_in_index_1755007910617_290];
                inj_out_array_sel_const_1755007910617_588 = my_array_ts1755007910618[inj_in_const_index_1755007910617_480];
            end
            // END: Mod_ArrayOps_ts1755007910618

            // BEGIN: case_priority_overlapping_mod_ts1755007910616
            always @* begin
                priority casez (sub_in_ts1755007910613)
                    2'b1?: inj_internal_out_1755007910616_975 = 5;
                    2'b?1: inj_internal_out_1755007910616_975 = 6;  
                    2'b0?: inj_internal_out_1755007910616_975 = 7;
                    2'b?0: inj_internal_out_1755007910616_975 = 8;  
                    default: inj_internal_out_1755007910616_975 = 9;
                endcase
            end
            // END: case_priority_overlapping_mod_ts1755007910616

            dup_cond dup_cond_inst_1755007910614_3814 (
                .data_b(inj_data_b_1755007910614_364),
                .result1(inj_result1_1755007910614_340),
                .result2(inj_result2_1755007910614_144),
                .control(inj_a_1755007910609_597),
                .data_a(inj_start_val_i_1755007910607_960)
            );
        ModuleBasic m_inst (
            .a      (1'b0),
            .b      (int'(sub_in_ts1755007910613)),
            .out_a  (),
            .out_b  (temp_int_ts1755007910613)
        );
        assign inj_data_out_1755007910613_899[i*4 +: 4] = temp_int_ts1755007910613[3:0];
    end
    // END: ModuleHierarchy_Low_ts1755007910613

    // BEGIN: target_module_for_bind_ts1755007910612
    always_comb inj_o_target_result_1755007910612_898 = inj_start_val_i_1755007910607_960 + 1;
    // END: target_module_for_bind_ts1755007910612

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
assign inj_test_case_result_1755007910610_87 = (inj_test_case_mode_1755007910610_756 == 2'b01) ? 4'h5 : 4'hA;
    // END: PragmaSyntaxVariety_ts1755007910611

    always @* begin
        inj_sum_1755007910609_147 = inj_a_1755007910609_597 + inj_b_1755007910609_69;
    end
    // END: CombinationalLogicImplicit_ts1755007910610

    always_ff @(posedge clk or negedge reset) begin
    if (!reset) begin
        inj_dffcl_data_out_1755007910608_793 <= 16'h0000;
    end else begin
        case (inj_dffcl_ctrl_mode_1755007910608_659)
            4'd0: inj_dffcl_data_out_1755007910608_793 <= inj_dffcl_data_in1_1755007910608_27 + inj_dffcl_data_in2_1755007910608_662;
            4'd1: begin
                if (inj_dffcl_data_in1_1755007910608_27 > inj_dffcl_data_in2_1755007910608_662) begin
                    case (inj_dffcl_ctrl_mode_1755007910608_659[1:0])
                        2'b00: inj_dffcl_data_out_1755007910608_793 <= inj_dffcl_data_in1_1755007910608_27 - inj_dffcl_data_in2_1755007910608_662;
                        2'b01: inj_dffcl_data_out_1755007910608_793 <= inj_dffcl_data_in1_1755007910608_27 & inj_dffcl_data_in2_1755007910608_662;
                        default: inj_dffcl_data_out_1755007910608_793 <= inj_dffcl_data_in1_1755007910608_27 | inj_dffcl_data_in2_1755007910608_662;
                    endcase
                end else begin
                    case (inj_dffcl_ctrl_mode_1755007910608_659[1:0])
                        2'b00: inj_dffcl_data_out_1755007910608_793 <= inj_dffcl_data_in2_1755007910608_662 - inj_dffcl_data_in1_1755007910608_27;
                        2'b01: inj_dffcl_data_out_1755007910608_793 <= inj_dffcl_data_in1_1755007910608_27 ^ inj_dffcl_data_in2_1755007910608_662;
                        default: inj_dffcl_data_out_1755007910608_793 <= ~inj_dffcl_data_in1_1755007910608_27;
                    endcase
                end
            end
            4'd2: begin
                casez (inj_dffcl_data_in1_1755007910608_27[15:13])
                    3'b000: inj_dffcl_data_out_1755007910608_793 <= inj_dffcl_data_in2_1755007910608_662;
                    3'b001: inj_dffcl_data_out_1755007910608_793 <= ~inj_dffcl_data_in2_1755007910608_662;
                    3'b01?: begin
                        if (inj_dffcl_data_in2_1755007910608_662[0]) inj_dffcl_data_out_1755007910608_793 <= inj_dffcl_data_in1_1755007910608_27 << 1;
                        else inj_dffcl_data_out_1755007910608_793 <= inj_dffcl_data_in1_1755007910608_27 >> 1;
                    end
                    3'b1??: begin
                        if (inj_dffcl_ctrl_mode_1755007910608_659[0]) inj_dffcl_data_out_1755007910608_793 <= inj_dffcl_data_in1_1755007910608_27 + 1;
                        else inj_dffcl_data_out_1755007910608_793 <= inj_dffcl_data_in1_1755007910608_27 - 1;
                    end
                    default: inj_dffcl_data_out_1755007910608_793 <= 16'hAAAA;
                endcase
            end
            default: begin
                if (inj_dffcl_ctrl_mode_1755007910608_659[2]) inj_dffcl_data_out_1755007910608_793 <= inj_dffcl_data_in1_1755007910608_27;
                else inj_dffcl_data_out_1755007910608_793 <= inj_dffcl_data_in2_1755007910608_662;
            end
        endcase
    end
    end
    // END: deep_ff_control_logic_ts1755007910609

    always @(posedge clk) begin
        inj_out2_a_1755007910608_473 <= inj_start_val_i_1755007910607_960;
    end
    // END: split_basic_nonblocking_ts1755007910608

    always @(posedge clk) begin
        inj_sum_out_i_1755007910607_590 <= 0;
        for (int i = 0; i < 4; i = i + 1) begin
            inj_sum_out_i_1755007910607_590 <= inj_sum_out_i_1755007910607_590 + inj_start_val_i_1755007910607_960 + i;
        end
    end
    // END: split_for_loop_ts1755007910608
endmodule

