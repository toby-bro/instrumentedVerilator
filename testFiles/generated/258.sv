interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
interface struct_if;
    logic [7:0] packet_field1;
    logic [7:0] packet_field2;
    logic tx_en;
    modport Access (output packet_field1, output packet_field2, output tx_en);
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

module concat_assign (
    input logic [7:0] in,
    output logic [3:0] out_h,
    output logic [3:0] out_l
);
    assign {out_h, out_l} = in;
endmodule

module configuration_top (
    input logic i_in,
    output logic o_out
);
    assign o_out = i_in;
endmodule

module deep_task_logic (
    input wire [1:0] dtl_action_sel,
    input wire dtl_clk,
    input wire [7:0] dtl_data_a,
    input wire [7:0] dtl_data_b,
    input wire dtl_en,
    input wire dtl_rst_n,
    output logic [7:0] dtl_result_reg
);
    task automatic perform_action;
        input [7:0] in_a;
        input [7:0] in_b;
        input [1:0] action;
        output logic [7:0] calculated_res;
        logic [7:0] temp_task_calc;
        if (action[0]) begin
            if (action[1]) begin
                temp_task_calc = in_a + in_b;
            end else begin
                temp_task_calc = in_a - in_b;
            end
        end else begin
            if (action[1]) begin
                temp_task_calc = in_a & in_b;
            end else begin
                temp_task_calc = in_a | in_b;
            end
        end
        case (temp_task_calc[1:0])
            2'b00: calculated_res = temp_task_calc ^ 8'hFF;
            2'b01: calculated_res = temp_task_calc + 1;
            2'b10: calculated_res = temp_task_calc - 1;
            default: calculated_res = temp_task_calc;
        endcase
    endtask
    always_ff @(posedge dtl_clk or negedge dtl_rst_n) begin
        if (!dtl_rst_n) begin
            dtl_result_reg <= 8'd0;
        end else begin
            logic [7:0] next_dtl_result;
            if (dtl_en) begin
                perform_action(dtl_data_a, dtl_data_b, dtl_action_sel, next_dtl_result);
            end else begin
                next_dtl_result = dtl_result_reg;
            end
            dtl_result_reg <= next_dtl_result;
        end
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

module mod_fixup_target (
    input logic fs_in_target,
    output logic fs_out_target
);
    assign fs_out_target = fs_in_target;
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

module module_with_param (
    input logic in,
    output logic named_out
);
    parameter int DELAY = 10;
    logic bind_dummy_in;
    logic bind_dummy_out;
    assign named_out = in;
endmodule

module module_assign_nonblocking (
    input logic clk,
    input logic [7:0] in_value,
    input logic reset,
    output logic out_data_q
);
    my_if vif_inst();
    logic [7:0] data_q;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            vif_inst.data <= 8'h0;
            data_q <= 8'h0;
        end else begin
            vif_inst.data <= in_value;
            data_q <= vif_inst.data;
        end
    end
    assign out_data_q = data_q;
endmodule

module nested_types_mod (
    input logic [31:0] nested_in,
    output logic [7:0] inner_field_o
);
    typedef struct packed {
        logic [7:0] inner_field;
        logic [7:0] padding;
    } inner_struct_t;
    typedef union packed {
        logic [31:0] full_word;
        struct packed {
            logic [15:0] unused;
            inner_struct_t inner_data;
        } outer_fields;
    } outer_union_t;
    outer_union_t nested_var;
    always_comb begin
        nested_var.full_word = nested_in;
    end
    assign inner_field_o = nested_var.outer_fields.inner_data.inner_field;
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

module module_struct_write (
    input logic [7:0] in_field1,
    input logic [7:0] in_field2,
    output logic tx_status
);
    struct_if stif_inst();
    always_comb begin
        stif_inst.packet_field1 = in_field1;
        stif_inst.packet_field2 = in_field2;
        stif_inst.tx_en = 1'b1;
        tx_status = stif_inst.tx_en;
    end
endmodule

module sub_inst_array_mod (
    input logic [7:0] in,
    output logic [7:0] out
);
    assign out = in;
endmodule

module super_outside_class_diag_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module udnt_port_module (
    input logic udnt_input,
    input logic uin,
    output logic udnt_output,
    output logic uout
);
    assign uout = uin;
    assign udnt_output = udnt_input;
endmodule

module snippet #(
    parameter int SEL_PARAM = 5
) (
    input wire clk,
    input logic [7:0] inj_a_1755007840656_182,
    input logic [7:0] inj_b_1755007840656_571,
    input logic inj_bind_in_1755007840655_151,
    input logic [7:0] inj_c_1755007840656_544,
    input logic [1:0] inj_case_expr_1755007840654_31,
    input logic [3:0] inj_data0_1755007840655_618,
    input logic [3:0] inj_data1_1755007840655_549,
    input logic [3:0] inj_data2_1755007840655_201,
    input logic [3:0] inj_data3_1755007840655_132,
    input wire [1:0] inj_dtl_action_sel_1755007840656_836,
    input wire [7:0] inj_dtl_data_b_1755007840656_73,
    input logic [15:0] inj_in1_1755007840660_316,
    input logic inj_in2_1755007840655_329,
    input logic [15:0] inj_in2_1755007840660_496,
    input logic [15:0] inj_in3_1755007840660_13,
    input logic [15:0] inj_in4_1755007840660_289,
    input logic [15:0] inj_in5_1755007840660_712,
    input wire [3:0] inj_in_a_1755007840655_705,
    input wire [3:0] inj_in_b_1755007840655_962,
    input wire [7:0] inj_in_c_1755007840655_326,
    input bit [3:0] inj_in_mask_z_1755007840694_820,
    input int inj_in_val_1755007840700_612,
    input logic [2:0] inj_index_1755007840729_818,
    input logic [31:0] inj_nested_in_1755007840658_532,
    input wire reset,
    output logic inj_anded_1755007840656_749,
    output logic inj_bind_out_1755007840655_766,
    output logic [7:0] inj_concat_out_1755007840717_14,
    output logic [7:0] inj_data_out_1755007840747_175,
    output logic [3:0] inj_data_out_1755007840765_351,
    output logic [3:0] inj_data_out_case_1755007840655_221,
    output logic inj_diff_1755007840656_510,
    output logic [7:0] inj_dtl_result_reg_1755007840656_266,
    output logic [7:0] inj_dtl_result_reg_1755007840662_706,
    output logic [7:0] inj_dtl_result_reg_1755007840682_238,
    output logic [7:0] inj_field2_o_1755007840723_89,
    output logic inj_fs_out_target_1755007840679_185,
    output logic [7:0] inj_inner_field_o_1755007840658_57,
    output logic [4:0] inj_internal_out_1755007840654_656,
    output wire inj_loop_out_1755007840660_565,
    output logic inj_named_out_1755007840689_92,
    output logic inj_o_out_1755007840711_856,
    output logic inj_o_result_1755007840775_423,
    output logic inj_ored_1755007840656_887,
    output logic inj_out_1755007840655_582,
    output logic inj_out_1755007840660_674,
    output logic [7:0] inj_out_1755007840676_945,
    output logic inj_out_1755007840729_507,
    output logic [15:0] inj_out_concat_1755007840655_201,
    output logic inj_out_data_q_1755007840673_360,
    output logic [7:0] inj_out_func_result_1755007840705_328,
    output logic [3:0] inj_out_h_1755007840734_425,
    output logic [7:0] inj_out_if_else_1755007840655_230,
    output logic [3:0] inj_out_l_1755007840734_190,
    output bit [1:0] inj_out_match_type_z_1755007840694_952,
    output logic [7:0] inj_out_reg_d_1755007840661_209,
    output reg inj_out_res_1755007840659_642,
    output int inj_out_val_1755007840700_63,
    output logic [7:0] inj_out_val_e_1755007840667_730,
    output logic [7:0] inj_out_var_1755007840756_922,
    output logic inj_status_e_1755007840667_292,
    output logic [7:0] inj_sum_1755007840656_329,
    output bit inj_system_status_clear_1755007840658_881,
    output logic inj_task_out_1755007840740_559,
    output logic [3:0] inj_test_case_result_1755007840669_840,
    output logic inj_tx_status_1755007840665_377,
    output logic inj_udnt_output_1755007840657_213,
    output logic inj_uout_1755007840657_468,
    output logic inj_xored_1755007840656_779,
    output logic inj_y_1755007840657_682
);
    // BEGIN: case_priority_overlapping_mod_ts1755007840654
    // BEGIN: bind_module_ts1755007840655
    // BEGIN: module_concat_if_ts1755007840655
    // BEGIN: simple_and_gate_ts1755007840655
    // BEGIN: case_selector_ts1755007840655
    // BEGIN: more_ops_ts1755007840656
    // BEGIN: mod_comb_logic_ts1755007840657
    // BEGIN: PragmaResetDirectives_ts1755007840658
`ifdef SLANG_PRAGMA
`reset protect diagnostic
`endif
    // BEGIN: case_single_default_after_item_ts1755007840659
    // BEGIN: Comb_Loop_ts1755007840660
    wire loop_wire1_ts1755007840660;
    wire loop_wire2_ts1755007840660;
        // BEGIN: deep_task_logic_ts1755007840684
        task automatic perform_action;
            input [7:0] in_a;
            input [7:0] in_b;
            input [1:0] action;
            output logic [7:0] calculated_res_ts1755007840684;
            logic [7:0] temp_task_calc_ts1755007840684;
            if (action[0]) begin
                if (action[1]) begin
                    temp_task_calc_ts1755007840684 = in_a + in_b;
                end else begin
                    temp_task_calc_ts1755007840684 = in_a - in_b;
                end
            end else begin
                if (action[1]) begin
                    temp_task_calc_ts1755007840684 = in_a & in_b;
                end else begin
                    temp_task_calc_ts1755007840684 = in_a | in_b;
                end
            end
            case (temp_task_calc_ts1755007840684[1:0])
                2'b00: calculated_res_ts1755007840684 = temp_task_calc_ts1755007840684 ^ 8'hFF;
                2'b01: calculated_res_ts1755007840684 = temp_task_calc_ts1755007840684 + 1;
                2'b10: calculated_res_ts1755007840684 = temp_task_calc_ts1755007840684 - 1;
                default: calculated_res_ts1755007840684 = temp_task_calc_ts1755007840684;
            endcase
        endtask
        always_ff @(posedge clk or negedge reset) begin
            if (!reset) begin
                inj_dtl_result_reg_1755007840682_238 <= 8'd0;
            end else begin
                logic [7:0] next_dtl_result_ts1755007840684;
                    // BEGIN: module_function_ts1755007840705
                    function automatic [7:0] add_and_subtract;
                    input [7:0] val1;
                    input [7:0] val2;
                    reg [7:0] temp_ts1755007840705;
                        // BEGIN: ModuleHierarchy_Low_ts1755007840748
                        ModuleBasic m1 (
                            .a     (1'b1),
                            .b     (inj_in_val_1755007840700_612),
                            .out_a (),
                            .out_b ( )
                        );
                        if (SEL_PARAM > 5) begin : gen_high
                            int high_data_ts1755007840747;
                            ModuleBasic m_high (
                                .a     (1'b0),
                                .b     (SEL_PARAM),
                                .out_a (),
                                .out_b (high_data_ts1755007840747)
                            );
                        end else begin : gen_low
                            int low_data_ts1755007840747;
                            ModuleBasic m_low (
                                .a     (1'b0),
                                .b     (SEL_PARAM),
                                .out_a (),
                                .out_b (low_data_ts1755007840747)
                            );
                        end
                        for (genvar i = 0; i < 2; ++i) begin : gen_loop
                            logic [1:0] sub_in_ts1755007840747;
                            assign sub_in_ts1755007840747 = inj_data2_1755007840655_201[i*2 +: 2];
                            int temp_int_ts1755007840747;
                                // BEGIN: not_a_hierarchical_scope_diag_mod_ts1755007840756
                                logic [7:0] simple_var_nahsdm_ts1755007840756;
                                    // BEGIN: sequential_logic_ts1755007840765
                                    ;
                                    logic [3:0] internal_reg_ts1755007840765;
                                        mod_simple_ref mod_simple_ref_inst_1755007840775_8223 (
                                            .i_data(inj_bind_in_1755007840655_151),
                                            .o_result(inj_o_result_1755007840775_423)
                                        );
                                    always_ff @(posedge clk or negedge reset) begin
                                        if (!reset) begin
                                            internal_reg_ts1755007840765 <= 4'h0;
                                        end else begin
                                            internal_reg_ts1755007840765 <= inj_data2_1755007840655_201;
                                        end
                                    end
                                    assign inj_data_out_1755007840765_351 = internal_reg_ts1755007840765;
                                    // END: sequential_logic_ts1755007840765

                                always_comb simple_var_nahsdm_ts1755007840756 = next_dtl_result_ts1755007840684;
                                assign inj_out_var_1755007840756_922 = simple_var_nahsdm_ts1755007840756;
                                // END: not_a_hierarchical_scope_diag_mod_ts1755007840756

                            ModuleBasic m_inst (
                                .a      (1'b0),
                                .b      (int'(sub_in_ts1755007840747)),
                                .out_a  (),
                                .out_b  (temp_int_ts1755007840747)
                            );
                            assign inj_data_out_1755007840747_175[i*4 +: 4] = temp_int_ts1755007840747[3:0];
                        end
                        // END: ModuleHierarchy_Low_ts1755007840748

                        // BEGIN: task_example_ts1755007840740
                        task automatic process_data (input logic data);
                            logic temp_ts1755007840740;
                            temp_ts1755007840740 = data; 
                        endtask 
                        assign inj_task_out_1755007840740_559 = inj_in2_1755007840655_329;
                        // END: task_example_ts1755007840740

                        concat_assign concat_assign_inst_1755007840734_8458 (
                            .out_l(inj_out_l_1755007840734_190),
                            .in(inj_c_1755007840656_544),
                            .out_h(inj_out_h_1755007840734_425)
                        );
                        // BEGIN: variable_sel_mux_ts1755007840729
                        assign inj_out_1755007840729_507 = inj_c_1755007840656_544[inj_index_1755007840729_818];
                        // END: variable_sel_mux_ts1755007840729

                        // BEGIN: typedef_struct_public_mod_ts1755007840723
                        typedef struct packed {
                            logic [7:0] field1_ts1755007840723;
                            logic [7:0] field2_ts1755007840723;
                        } my_public_packed_struct_t;
                        my_public_packed_struct_t my_struct_var;
                        always_comb begin
                            my_struct_var = inj_in3_1755007840660_13;
                        end
                        assign inj_field2_o_1755007840723_89 = my_struct_var.field2_ts1755007840723;
                        // END: typedef_struct_public_mod_ts1755007840723

                        macro_concat_user macro_concat_user_inst_1755007840717_9753 (
                            .concat_out(inj_concat_out_1755007840717_14),
                            .concat_in(inj_data2_1755007840655_201)
                        );
                        configuration_top configuration_top_inst_1755007840711_9272 (
                            .i_in(inj_in2_1755007840655_329),
                            .o_out(inj_o_out_1755007840711_856)
                        );
                    begin
                    temp_ts1755007840705 = val1 + val2;
                    add_and_subtract = temp_ts1755007840705 - 1;
                    end
                    endfunction
                    always_comb begin
                    inj_out_func_result_1755007840705_328 = add_and_subtract(inj_in_c_1755007840655_326, inj_dtl_data_b_1755007840656_73);
                    end
                    // END: module_function_ts1755007840705

                    super_outside_class_diag_mod super_outside_class_diag_mod_inst_1755007840700_6845 (
                        .in_val(inj_in_val_1755007840700_612),
                        .out_val(inj_out_val_1755007840700_63)
                    );
                    // BEGIN: mod_casez_wildcard_ts1755007840694
                always_comb begin
                    casez (inj_in_mask_z_1755007840694_820)
                        4'b10?0: begin
                            inj_out_match_type_z_1755007840694_952 = 2'b00;
                        end
                        4'b011?: begin
                            inj_out_match_type_z_1755007840694_952 = 2'b01;
                        end
                        default: begin
                            inj_out_match_type_z_1755007840694_952 = 2'b11;
                        end
                    endcase
                end
                    // END: mod_casez_wildcard_ts1755007840694

                    module_with_param module_with_param_inst_1755007840689_5262 (
                        .named_out(inj_named_out_1755007840689_92),
                        .in(inj_bind_in_1755007840655_151)
                    );
                if (reset) begin
                    perform_action(inj_dtl_data_b_1755007840656_73, inj_in_c_1755007840655_326, inj_dtl_action_sel_1755007840656_836, next_dtl_result_ts1755007840684);
                end else begin
                    next_dtl_result_ts1755007840684 = inj_dtl_result_reg_1755007840682_238;
                end
                inj_dtl_result_reg_1755007840682_238 <= next_dtl_result_ts1755007840684;
            end
        end
        // END: deep_task_logic_ts1755007840684

        mod_fixup_target mod_fixup_target_inst_1755007840679_1604 (
            .fs_out_target(inj_fs_out_target_1755007840679_185),
            .fs_in_target(inj_bind_in_1755007840655_151)
        );
        sub_inst_array_mod sub_inst_array_mod_inst_1755007840676_691 (
            .in(inj_c_1755007840656_544),
            .out(inj_out_1755007840676_945)
        );
        module_assign_nonblocking module_assign_nonblocking_inst_1755007840673_5734 (
            .out_data_q(inj_out_data_q_1755007840673_360),
            .clk(clk),
            .in_value(inj_b_1755007840656_571),
            .reset(reset)
        );
        // BEGIN: PragmaSyntaxVariety_ts1755007840670
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
    assign inj_test_case_result_1755007840669_840 = (inj_case_expr_1755007840654_31 == 2'b01) ? 4'h5 : 4'hA;
        // END: PragmaSyntaxVariety_ts1755007840670

        split_mixed_cond_seq split_mixed_cond_seq_inst_1755007840667_9050 (
            .out_val_e(inj_out_val_e_1755007840667_730),
            .status_e(inj_status_e_1755007840667_292),
            .clk_e(clk),
            .condition_e(inj_bind_in_1755007840655_151),
            .in_override_e(inj_a_1755007840656_182),
            .in_val_e(inj_c_1755007840656_544)
        );
        module_struct_write module_struct_write_inst_1755007840665_606 (
            .in_field2(inj_c_1755007840656_544),
            .tx_status(inj_tx_status_1755007840665_377),
            .in_field1(inj_a_1755007840656_182)
        );
        deep_task_logic deep_task_logic_inst_1755007840662_7212 (
            .dtl_result_reg(inj_dtl_result_reg_1755007840662_706),
            .dtl_action_sel(inj_dtl_action_sel_1755007840656_836),
            .dtl_clk(clk),
            .dtl_data_a(inj_dtl_data_b_1755007840656_73),
            .dtl_data_b(inj_in_c_1755007840655_326),
            .dtl_en(loop_wire1_ts1755007840660),
            .dtl_rst_n(reset)
        );
        // BEGIN: split_conditional_nb_ts1755007840661
        always @(posedge clk) begin
            if (inj_in2_1755007840655_329) begin
                inj_out_reg_d_1755007840661_209 <= inj_a_1755007840656_182;
            end else begin
                inj_out_reg_d_1755007840661_209 <= inj_c_1755007840656_544;
            end
        end
        // END: split_conditional_nb_ts1755007840661

        // BEGIN: arith_comp_ops_ts1755007840661
        assign inj_out_1755007840660_674 = (inj_in1_1755007840660_316 + inj_in2_1755007840660_496) * inj_in3_1755007840660_13 > inj_in4_1755007840660_289 - inj_in5_1755007840660_712;
        // END: arith_comp_ops_ts1755007840661

    assign loop_wire1_ts1755007840660 = loop_wire2_ts1755007840660 | reset;
    assign loop_wire2_ts1755007840660 = loop_wire1_ts1755007840660; 
    assign inj_loop_out_1755007840660_565 = loop_wire1_ts1755007840660;
    // END: Comb_Loop_ts1755007840660

    always_comb begin
        inj_out_res_1755007840659_642 = 1'b0;
        case (inj_case_expr_1755007840654_31)
            2'b01: inj_out_res_1755007840659_642 = 1'b1;
            default: inj_out_res_1755007840659_642 = 1'b0;
            2'b10: inj_out_res_1755007840659_642 = 1'b1;
        endcase
    end
    // END: case_single_default_after_item_ts1755007840659

assign inj_system_status_clear_1755007840658_881 = reset;
    // END: PragmaResetDirectives_ts1755007840658

    nested_types_mod nested_types_mod_inst_1755007840658_2694 (
        .nested_in(inj_nested_in_1755007840658_532),
        .inner_field_o(inj_inner_field_o_1755007840658_57)
    );
    always_comb begin
        inj_y_1755007840657_682 = inj_bind_in_1755007840655_151 & inj_in2_1755007840655_329;
    end
    // END: mod_comb_logic_ts1755007840657

    udnt_port_module udnt_port_module_inst_1755007840657_6965 (
        .uout(inj_uout_1755007840657_468),
        .udnt_input(inj_bind_in_1755007840655_151),
        .uin(inj_in2_1755007840655_329),
        .udnt_output(inj_udnt_output_1755007840657_213)
    );
    deep_task_logic deep_task_logic_inst_1755007840656_9052 (
        .dtl_data_b(inj_dtl_data_b_1755007840656_73),
        .dtl_en(reset),
        .dtl_rst_n(reset),
        .dtl_result_reg(inj_dtl_result_reg_1755007840656_266),
        .dtl_action_sel(inj_dtl_action_sel_1755007840656_836),
        .dtl_clk(clk),
        .dtl_data_a(inj_in_c_1755007840655_326)
    );
    assign inj_sum_1755007840656_329 = inj_a_1755007840656_182 + inj_b_1755007840656_571;
    assign inj_diff_1755007840656_510 = inj_a_1755007840656_182 > inj_c_1755007840656_544;
    assign inj_anded_1755007840656_749 = inj_a_1755007840656_182 & inj_b_1755007840656_571;
    assign inj_ored_1755007840656_887 = inj_a_1755007840656_182 | inj_c_1755007840656_544;
    assign inj_xored_1755007840656_779 = inj_a_1755007840656_182 ^ inj_b_1755007840656_571;
    // END: more_ops_ts1755007840656

    always_comb begin
        case (inj_case_expr_1755007840654_31)
            2'b00: inj_data_out_case_1755007840655_221 = inj_data0_1755007840655_618; 
            2'b01: inj_data_out_case_1755007840655_221 = inj_data1_1755007840655_549; 
            2'b10: inj_data_out_case_1755007840655_221 = inj_data2_1755007840655_201; 
            default: inj_data_out_case_1755007840655_221 = inj_data3_1755007840655_132; 
        endcase
    end
    // END: case_selector_ts1755007840655

    assign inj_out_1755007840655_582 = inj_bind_in_1755007840655_151 & inj_in2_1755007840655_329;
    // END: simple_and_gate_ts1755007840655

    always_comb begin
    inj_out_concat_1755007840655_201 = {inj_in_a_1755007840655_705, inj_in_b_1755007840655_962, inj_in_c_1755007840655_326};
    if (reset) begin
        inj_out_if_else_1755007840655_230 = inj_in_c_1755007840655_326;
    end else begin
        inj_out_if_else_1755007840655_230 = {inj_in_a_1755007840655_705, inj_in_b_1755007840655_962};
    end
    end
    // END: module_concat_if_ts1755007840655

    assign inj_bind_out_1755007840655_766 = inj_bind_in_1755007840655_151;
    // END: bind_module_ts1755007840655

    always @* begin
        priority casez (inj_case_expr_1755007840654_31)
            2'b1?: inj_internal_out_1755007840654_656 = 5;
            2'b?1: inj_internal_out_1755007840654_656 = 6;  
            2'b0?: inj_internal_out_1755007840654_656 = 7;
            2'b?0: inj_internal_out_1755007840654_656 = 8;  
            default: inj_internal_out_1755007840654_656 = 9;
        endcase
    end
    // END: case_priority_overlapping_mod_ts1755007840654
endmodule

