module ModClockedWithSimpleAssign (
    input logic clk,
    input logic in_a,
    input logic in_b,
    output logic out_comb,
    output logic out_reg
);
    logic internal_reg;
    always @(posedge clk) begin 
    internal_reg <= in_a; 
    end
    assign out_comb = in_a ^ in_b; 
    always @(posedge clk) begin 
    out_reg <= internal_reg & in_b; 
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

module ModuleComb (
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic [7:0] out1,
    output logic [7:0] out2
);
    logic [7:0] internal_wire;
    assign internal_wire = in1 + in2;
    always_comb begin
        if (internal_wire > 8'd128) begin
            out1 = internal_wire - 1;
        end else begin
            out1 = internal_wire + 1;
        end
        out2 = internal_wire / 2;
    end
endmodule

module ModuleHierarchy_Low #(
    parameter int SEL_PARAM = 5
) (
    input logic [3:0] data_in,
    input int sel_in,
    output logic [7:0] data_out
);
    ModuleBasic m1 (
        .a     (1'b1),
        .b     (sel_in),
        .out_a (),
        .out_b ( )
    );
    if (SEL_PARAM > 5) begin : gen_high
        int high_data;
        ModuleBasic m_high (
            .a     (1'b0),
            .b     (SEL_PARAM),
            .out_a (),
            .out_b (high_data)
        );
    end else begin : gen_low
        int low_data;
        ModuleBasic m_low (
            .a     (1'b0),
            .b     (SEL_PARAM),
            .out_a (),
            .out_b (low_data)
        );
    end
    for (genvar i = 0; i < 2; ++i) begin : gen_loop
        logic [1:0] sub_in;
        assign sub_in = data_in[i*2 +: 2];
        int temp_int;
        ModuleBasic m_inst (
            .a      (1'b0),
            .b      (int'(sub_in)),
            .out_a  (),
            .out_b  (temp_int)
        );
        assign data_out[i*4 +: 4] = temp_int[3:0];
    end
endmodule

module mod_name_conflict (
    input logic in_a,
    output logic out_a
);
    logic conflict_var;
    parameter int conflict_param = 1;
    assign out_a = in_a;
endmodule

module module_function (
    input wire [7:0] in_func_a,
    input wire [7:0] in_func_b,
    output logic [7:0] out_func_result
);
    function automatic [7:0] add_and_subtract;
    input [7:0] val1;
    input [7:0] val2;
    reg [7:0] temp;
    begin
    temp = val1 + val2;
    add_and_subtract = temp - 1;
    end
    endfunction
    always_comb begin
    out_func_result = add_and_subtract(in_func_a, in_func_b);
    end
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

module sub_inst_array_mod (
    input logic [7:0] in,
    output logic [7:0] out
);
    assign out = in;
endmodule

module snippet (
    input wire clk,
    input logic inj_a_1755007849830_490,
    input int inj_b_1755007849830_449,
    input logic [3:0] inj_case_inside_val_1755007849830_298,
    input wire inj_g_in_1755007849839_982,
    input logic [7:0] inj_i2_s_1755007849833_124,
    input logic [7:0] inj_i3_s_1755007849833_830,
    input logic [7:0] inj_in_1755007849830_654,
    input wire [7:0] inj_in_func_a_1755007849844_385,
    input wire [7:0] inj_in_func_b_1755007849844_374,
    input wire reset,
    output int inj_config_data_out_1755007849832_566,
    output logic [7:0] inj_data_out_1755007849832_866,
    output logic [7:0] inj_data_out_1755007849833_900,
    output logic [7:0] inj_data_out_1755007849837_482,
    output wire inj_g_out_and_1755007849839_33,
    output wire inj_g_out_or_1755007849839_605,
    output logic [4:0] inj_internal_out_1755007849830_791,
    output wire inj_loop_out_1755007849841_761,
    output logic inj_nm_out_1755007849836_549,
    output logic [7:0] inj_o1_s_1755007849833_398,
    output logic [7:0] inj_o2_s_1755007849833_698,
    output logic [7:0] inj_o3_s_1755007849833_423,
    output logic [7:0] inj_out1_1755007849848_195,
    output logic [7:0] inj_out2_1755007849848_765,
    output logic [7:0] inj_out_1755007849830_40,
    output logic inj_out_a_1755007849830_74,
    output logic inj_out_a_1755007849830_974,
    output int inj_out_b_1755007849830_387,
    output logic inj_out_bit_1755007849831_551,
    output logic inj_out_comb_1755007849851_925,
    output logic [7:0] inj_out_func_result_1755007849844_71,
    output logic inj_out_la_1755007849831_513,
    output logic inj_out_pd_1755007849834_722,
    output logic inj_out_reg_1755007849851_68,
    output logic [7:0] inj_out_reg_d_1755007849835_915,
    output logic [7:0] inj_out_reg_p_1755007849846_254,
    output logic [7:0] inj_out_val_e_1755007849835_798,
    output logic [7:0] inj_out_var_1755007849855_31,
    output logic inj_q_out_1755007849843_402,
    output logic inj_status_e_1755007849835_10,
    output logic inj_tok_out_1755007849840_718,
    output logic inj_udnt_output_1755007849831_309,
    output logic inj_uout_1755007849831_612
);
    // BEGIN: case_parallel_simple_mod_ts1755007849830
    // BEGIN: ModuleBasic_ts1755007849830
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c_ts1755007849830;
    int   d_ts1755007849830;
    always_comb begin
        logic temp_v_ts1755007849830;
            // BEGIN: split_complex_nb_ts1755007849833
            logic [7:0] t1_s_ts1755007849833, t2_s_ts1755007849833;
                // BEGIN: SequentialLogic_ts1755007849837
                logic [7:0] internal_reg_ts1755007849837;
                    // BEGIN: Comb_Loop_ts1755007849841
                    wire loop_wire1_ts1755007849841;
                    wire loop_wire2_ts1755007849841;
                        // BEGIN: LogicDependencyChain_ts1755007849843
                        logic q1_ts1755007849843, q2_ts1755007849843;
                            // BEGIN: not_a_hierarchical_scope_diag_mod_ts1755007849856
                            logic [7:0] simple_var_nahsdm_ts1755007849855;
                            always_comb simple_var_nahsdm_ts1755007849855 = inj_i2_s_1755007849833_124;
                            assign inj_out_var_1755007849855_31 = simple_var_nahsdm_ts1755007849855;
                            // END: not_a_hierarchical_scope_diag_mod_ts1755007849856

                            ModClockedWithSimpleAssign ModClockedWithSimpleAssign_inst_1755007849851_57 (
                                .clk(clk),
                                .in_a(inj_a_1755007849830_490),
                                .in_b(q2_ts1755007849843),
                                .out_comb(inj_out_comb_1755007849851_925),
                                .out_reg(inj_out_reg_1755007849851_68)
                            );
                            ModuleComb ModuleComb_inst_1755007849848_3112 (
                                .in2(inj_i3_s_1755007849833_830),
                                .out1(inj_out1_1755007849848_195),
                                .out2(inj_out2_1755007849848_765),
                                .in1(inj_in_1755007849830_654)
                            );
                            // BEGIN: split_if_empty_then_ts1755007849846
                            always @(posedge clk) begin
                                if (temp_v_ts1755007849830) begin
                                end else begin
                                    inj_out_reg_p_1755007849846_254 <= t2_s_ts1755007849833;
                                end
                            end
                            // END: split_if_empty_then_ts1755007849846

                            module_function module_function_inst_1755007849844_5305 (
                                .in_func_a(inj_in_func_a_1755007849844_385),
                                .in_func_b(inj_in_func_b_1755007849844_374),
                                .out_func_result(inj_out_func_result_1755007849844_71)
                            );
                        always @(posedge clk) begin
                            q1_ts1755007849843 <= inj_a_1755007849830_490;
                        end
                        always @(q1_ts1755007849843) begin
                            q2_ts1755007849843 = ~q1_ts1755007849843;
                        end
                        assign inj_q_out_1755007849843_402 = q2_ts1755007849843;
                        // END: LogicDependencyChain_ts1755007849843

                    assign loop_wire1_ts1755007849841 = loop_wire2_ts1755007849841 | inj_g_in_1755007849839_982;
                    assign loop_wire2_ts1755007849841 = loop_wire1_ts1755007849841; 
                    assign inj_loop_out_1755007849841_761 = loop_wire1_ts1755007849841;
                    // END: Comb_Loop_ts1755007849841

                    // BEGIN: Module_MacroTokens_ts1755007849840
                    `define PASTE(a,b) a``b
                    logic `PASTE(my,_var);
                    always_comb begin
                        `PASTE(my,_var) = temp_v_ts1755007849830;
                        inj_tok_out_1755007849840_718         = `PASTE(my,_var);
                    end
                    // END: Module_MacroTokens_ts1755007849840

                    // BEGIN: Module_GatePrimitives_ts1755007849839
                    and a1 (inj_g_out_and_1755007849839_33, inj_g_in_1755007849839_982, inj_g_in_1755007849839_982);
                    or  o1 (inj_g_out_or_1755007849839_605 , inj_g_in_1755007849839_982, inj_g_in_1755007849839_982);
                    // END: Module_GatePrimitives_ts1755007849839

                always @(posedge clk or negedge reset) begin
                    if (~reset) begin
                        internal_reg_ts1755007849837 <= 8'h00;
                    end else begin
                        internal_reg_ts1755007849837 <= inj_i2_s_1755007849833_124;
                    end
                end
                assign inj_data_out_1755007849837_482 = internal_reg_ts1755007849837;
                // END: SequentialLogic_ts1755007849837

                // BEGIN: nested_module_ts1755007849836
                assign inj_nm_out_1755007849836_549 = inj_a_1755007849830_490;
                // END: nested_module_ts1755007849836

                split_mixed_cond_seq split_mixed_cond_seq_inst_1755007849835_6860 (
                    .in_val_e(t1_s_ts1755007849833),
                    .out_val_e(inj_out_val_e_1755007849835_798),
                    .status_e(inj_status_e_1755007849835_10),
                    .clk_e(clk),
                    .condition_e(temp_v_ts1755007849830),
                    .in_override_e(inj_in_1755007849830_654)
                );
                // BEGIN: split_conditional_nb_ts1755007849835
                always @(posedge clk) begin
                    if (temp_v_ts1755007849830) begin
                        inj_out_reg_d_1755007849835_915 <= t1_s_ts1755007849833;
                    end else begin
                        inj_out_reg_d_1755007849835_915 <= inj_in_1755007849830_654;
                    end
                end
                // END: split_conditional_nb_ts1755007849835

                // BEGIN: ProgramDefinition_ts1755007849834
                assign inj_out_pd_1755007849834_722 = clk;
                // END: ProgramDefinition_ts1755007849834

            always @(posedge clk) begin
                t1_s_ts1755007849833 <= inj_in_1755007849830_654 + inj_i2_s_1755007849833_124;
                inj_o1_s_1755007849833_398 <= t1_s_ts1755007849833 - inj_i3_s_1755007849833_830;
                t2_s_ts1755007849833 <= inj_i2_s_1755007849833_124 * inj_i3_s_1755007849833_830;
                inj_o2_s_1755007849833_698 <= t1_s_ts1755007849833 + t2_s_ts1755007849833;
                inj_o3_s_1755007849833_423 <= t2_s_ts1755007849833 / 2;
            end
            // END: split_complex_nb_ts1755007849833

            // BEGIN: cu_base_ts1755007849833
            assign inj_data_out_1755007849833_900 = inj_in_1755007849830_654;
            // END: cu_base_ts1755007849833

            // BEGIN: PragmaProtectOptions_ts1755007849832
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
        assign inj_config_data_out_1755007849832_566 = d_ts1755007849830 + 1;
            // END: PragmaProtectOptions_ts1755007849832

            ModuleHierarchy_Low ModuleHierarchy_Low_inst_1755007849832_6106 (
                .data_out(inj_data_out_1755007849832_866),
                .data_in(inj_case_inside_val_1755007849830_298),
                .sel_in(d_ts1755007849830)
            );
            // BEGIN: udnt_port_module_ts1755007849831
            assign inj_uout_1755007849831_612 = inj_a_1755007849830_490;
            assign inj_udnt_output_1755007849831_309 = temp_v_ts1755007849830;
            // END: udnt_port_module_ts1755007849831

            // BEGIN: mod_large_array_target_ts1755007849831
            assign inj_out_la_1755007849831_513 = inj_a_1755007849830_490;
            // END: mod_large_array_target_ts1755007849831

            // BEGIN: recursive_macro_dummy_ts1755007849831
            `define RECURSIVE_TEST `RECURSIVE_TEST
            assign inj_out_bit_1755007849831_551 = inj_a_1755007849830_490;
            // END: recursive_macro_dummy_ts1755007849831

            mod_name_conflict mod_name_conflict_inst_1755007849830_6585 (
                .out_a(inj_out_a_1755007849830_74),
                .in_a(inj_a_1755007849830_490)
            );
        temp_v_ts1755007849830 = d_ts1755007849830;
        c_ts1755007849830      = temp_v_ts1755007849830;
    end
    assign inj_out_a_1755007849830_974 = inj_a_1755007849830_490;
    assign d_ts1755007849830     = inj_b_1755007849830_449;
    assign inj_out_b_1755007849830_387 = d_ts1755007849830 + P1 + LP1;
    // END: ModuleBasic_ts1755007849830

    always @* begin
        (* parallel *)
        case (inj_case_inside_val_1755007849830_298)
            4'd0, 4'd1: inj_internal_out_1755007849830_791 = 14;
            4'd2, 4'd3: inj_internal_out_1755007849830_791 = 15;
            default: inj_internal_out_1755007849830_791 = 18;
        endcase
    end
    // END: case_parallel_simple_mod_ts1755007849830

    sub_inst_array_mod sub_inst_array_mod_inst_1755007849830_779 (
        .in(inj_in_1755007849830_654),
        .out(inj_out_1755007849830_40)
    );
endmodule

