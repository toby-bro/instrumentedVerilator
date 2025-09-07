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

module PragmaOnceDirective (
    input bit trigger_input,
    output bit trigger_output
);
assign trigger_output = trigger_input;
endmodule

module child_module_v2_config_dummy (
    input logic i,
    output logic o
);
    assign o = i | i; 
endmodule

module split_case (
    input logic clk_w,
    input logic [7:0] d0_w,
    input logic [7:0] d1_w,
    input logic [7:0] d2_w,
    input logic [7:0] d3_w,
    input logic [1:0] sel_w,
    output logic [7:0] out_w
);
    always @(posedge clk_w) begin
        case (sel_w)
            2'b00: out_w <= d0_w;
            2'b01: out_w <= d1_w;
            2'b10: out_w <= d2_w;
            default: out_w <= d3_w;
        endcase
    end
endmodule

module split_reorder_blocking (
    input logic [7:0] in_a_g,
    input logic [7:0] in_b_g,
    output logic [7:0] out_p_g,
    output logic [7:0] out_q_g
);
    logic [7:0] mid_x_g;
    logic [7:0] mid_y_g;
    always @(*) begin
        mid_x_g = in_a_g * 2;
        mid_y_g = mid_x_g + in_b_g;
        out_p_g = mid_y_g - 1;
        out_q_g = mid_x_g / 2;
    end
endmodule

module snippet (
    input wire clk,
    input int inj_b_1755007782840_428,
    input logic [1:0] inj_case_expr_1755007782839_849,
    input logic [3:0] inj_case_inside_val_1755007782839_458,
    input logic [7:0] inj_d2_w_1755007782845_430,
    input logic [7:0] inj_d3_w_1755007782845_180,
    input bit [7:0] inj_data1_1755007782852_835,
    input bit [7:0] inj_data2_1755007782852_534,
    input wire [3:0] inj_data_c_1755007782855_770,
    input logic inj_i_1755007782839_404,
    input logic [7:0] inj_in_field1_1755007782841_770,
    input logic [7:0] inj_in_field2_1755007782841_480,
    input logic inj_in_k_1755007782842_187,
    input logic [15:0] inj_packed_in_1755007782840_19,
    input logic [2:0] inj_selector_1755007782848_343,
    input wire [1:0] inj_selector_1755007782855_495,
    input bit inj_trigger_input_1755007782839_881,
    input wire reset,
    output logic inj_dout_a_1755007782843_174,
    output logic inj_dout_b_1755007782843_896,
    output logic inj_dummy_1755007782843_696,
    output logic inj_dummy_out_non_ansi_1755007782849_948,
    output logic [7:0] inj_field2_o_1755007782840_653,
    output logic [4:0] inj_internal_out_1755007782839_746,
    output logic [4:0] inj_internal_out_1755007782847_82,
    output logic inj_named_conn_out_1755007782849_990,
    output logic inj_o_1755007782839_621,
    output logic inj_o_1755007782846_90,
    output logic [7:0] inj_o_target_result_1755007782854_283,
    output logic inj_out_a_1755007782840_485,
    output logic inj_out_a_1755007782840_895,
    output int inj_out_b_1755007782840_518,
    output int inj_out_b_1755007782840_847,
    output logic [3:0] inj_out_case_case_1755007782855_783,
    output logic [3:0] inj_out_case_casex_1755007782855_514,
    output logic [3:0] inj_out_case_casez_1755007782855_931,
    output logic inj_out_l_1755007782842_32,
    output logic [7:0] inj_out_p_g_1755007782844_4,
    output logic [7:0] inj_out_q_g_1755007782844_280,
    output logic [7:0] inj_out_val_1755007782851_288,
    output logic [7:0] inj_out_w_1755007782845_234,
    output bit [7:0] inj_result1_1755007782852_736,
    output bit [7:0] inj_result2_1755007782852_66,
    output logic [3:0] inj_result_out_1755007782848_853,
    output bit inj_trigger_output_1755007782839_345,
    output logic inj_tx_status_1755007782841_985
);
    // BEGIN: top_module_config_dummy_ts1755007782839
    // BEGIN: case_priority_casex_complex_mod_ts1755007782839
    // BEGIN: typedef_struct_mod_ts1755007782841
    typedef struct packed {
        logic [7:0] field1_ts1755007782841;
        logic [7:0] field2_ts1755007782841;
    } my_packed_struct_t;
    my_packed_struct_t my_struct_var;
    // BEGIN: explicit_non_ansi_ports_module_ts1755007782850
    input logic inj_i_1755007782839_404_ts1755007782849;
    output logic inj_named_conn_out_1755007782849_990_ts1755007782849;
    input logic inj_in_k_1755007782842_187_ts1755007782849;
    output logic inj_dummy_out_non_ansi_1755007782849_948_ts1755007782849;
    // BEGIN: CaseStatementConditions_ts1755007782856
    always_comb begin
        case (inj_selector_1755007782855_495)
            2'b00: inj_out_case_case_1755007782855_783 = inj_data_c_1755007782855_770;
            2'b01: inj_out_case_case_1755007782855_783 = inj_data_c_1755007782855_770 + 1;
            2'b10: inj_out_case_case_1755007782855_783 = inj_data_c_1755007782855_770 + 2;
            default: inj_out_case_case_1755007782855_783 = 4'bxxxx;
        endcase
        casez (inj_selector_1755007782855_495)
            2'b0?: inj_out_case_casez_1755007782855_931 = inj_data_c_1755007782855_770 + 10;
            2'b1?: inj_out_case_casez_1755007782855_931 = inj_data_c_1755007782855_770 + 20;
            default: inj_out_case_casez_1755007782855_931 = 4'bzzzz;
        endcase
        casex (inj_selector_1755007782855_495)
            2'b0?: inj_out_case_casex_1755007782855_514 = inj_data_c_1755007782855_770 - 1;
            2'b1?: inj_out_case_casex_1755007782855_514 = inj_data_c_1755007782855_770 - 2;
            default: inj_out_case_casex_1755007782855_514 = 4'bxxxx;
        endcase
    end
    // END: CaseStatementConditions_ts1755007782856

    // BEGIN: target_module_for_bind_ts1755007782854
    always_comb inj_o_target_result_1755007782854_283 = inj_in_field2_1755007782841_480 + 1;
    // END: target_module_for_bind_ts1755007782854

    // BEGIN: comb_conditional_ts1755007782852
    always @* begin
        if (inj_trigger_input_1755007782839_881) begin
            inj_result1_1755007782852_736 = inj_data1_1755007782852_835;
            inj_result2_1755007782852_66 = inj_data1_1755007782852_835;
        end else begin
            inj_result1_1755007782852_736 = inj_data2_1755007782852_534;
            inj_result2_1755007782852_66 = inj_data2_1755007782852_534;
        end
    end
    // END: comb_conditional_ts1755007782852

    // BEGIN: generic_class_scope_diag_mod_ts1755007782851
    assign inj_out_val_1755007782851_288 = inj_in_field2_1755007782841_480;
    // END: generic_class_scope_diag_mod_ts1755007782851

    assign inj_named_conn_out_1755007782849_990_ts1755007782849 = inj_i_1755007782839_404_ts1755007782849;
    assign inj_dummy_out_non_ansi_1755007782849_948_ts1755007782849 = inj_in_k_1755007782842_187_ts1755007782849;
    // END: explicit_non_ansi_ports_module_ts1755007782850

    // BEGIN: rand_case_mod_ts1755007782848
    always_comb begin
        case (inj_selector_1755007782848_343)
            0: inj_result_out_1755007782848_853 = 4'h0;
            1: inj_result_out_1755007782848_853 = 4'h1;
            2: inj_result_out_1755007782848_853 = 4'hA;
            default: inj_result_out_1755007782848_853 = 4'hF;
        endcase
    end
    // END: rand_case_mod_ts1755007782848

    // BEGIN: case_priority_casex_complex_mod_ts1755007782847
    always @* begin
        priority casex ({inj_case_expr_1755007782839_849, inj_case_inside_val_1755007782839_458[1:0]})
            4'b1???: inj_internal_out_1755007782847_82 = 24;
            4'b?1??: inj_internal_out_1755007782847_82 = 25;  
            4'b??1?: inj_internal_out_1755007782847_82 = 26;  
            4'b???1: inj_internal_out_1755007782847_82 = 27;  
            4'b0000: inj_internal_out_1755007782847_82 = 28;  
            default: inj_internal_out_1755007782847_82 = 29;
        endcase
    end
    // END: case_priority_casex_complex_mod_ts1755007782847

    child_module_v2_config_dummy child_module_v2_config_dummy_inst_1755007782846_1135 (
        .o(inj_o_1755007782846_90),
        .i(inj_i_1755007782839_404)
    );
    split_case split_case_inst_1755007782845_7765 (
        .d3_w(inj_d3_w_1755007782845_180),
        .sel_w(inj_case_expr_1755007782839_849),
        .out_w(inj_out_w_1755007782845_234),
        .clk_w(clk),
        .d0_w(inj_in_field2_1755007782841_480),
        .d1_w(inj_in_field1_1755007782841_770),
        .d2_w(inj_d2_w_1755007782845_430)
    );
    split_reorder_blocking split_reorder_blocking_inst_1755007782844_7562 (
        .in_b_g(inj_in_field2_1755007782841_480),
        .out_p_g(inj_out_p_g_1755007782844_4),
        .out_q_g(inj_out_q_g_1755007782844_280),
        .in_a_g(inj_in_field1_1755007782841_770)
    );
    // BEGIN: ModMultipleAlways_ts1755007782843
    always @(posedge clk or negedge reset) begin 
    if (!reset) begin 
        inj_dout_a_1755007782843_174 <= 1'b0;
    end else begin
        inj_dout_a_1755007782843_174 <= inj_in_k_1755007782842_187; 
    end
    end
    always @(posedge clk) begin 
    inj_dout_b_1755007782843_896 <= inj_i_1755007782839_404; 
    end
    // END: ModMultipleAlways_ts1755007782843

    // BEGIN: mod_err_event_constant_ts1755007782843
    always @(posedge 1'b1) begin
        inj_dummy_1755007782843_696 = ~inj_dummy_1755007782843_696;
    end
    // END: mod_err_event_constant_ts1755007782843

    // BEGIN: LintLatch_ts1755007782842
    always_comb begin
        if (inj_i_1755007782839_404) begin
            inj_out_l_1755007782842_32 = inj_in_k_1755007782842_187;
        end else begin
            inj_out_l_1755007782842_32 = 1'b0; 
        end
    end
    // END: LintLatch_ts1755007782842

    // BEGIN: module_struct_write_ts1755007782841
    struct_if stif_inst();
    always_comb begin
        stif_inst.packet_field1 = inj_in_field1_1755007782841_770;
        stif_inst.packet_field2 = inj_in_field2_1755007782841_480;
        stif_inst.tx_en = 1'b1;
        inj_tx_status_1755007782841_985 = stif_inst.tx_en;
    end
    // END: module_struct_write_ts1755007782841

    always_comb begin
        my_struct_var = inj_packed_in_1755007782840_19;
    end
    assign inj_field2_o_1755007782840_653 = my_struct_var.field2_ts1755007782841;
    // END: typedef_struct_mod_ts1755007782841

    ModuleBasic ModuleBasic_inst_1755007782840_5808 (
        .a(inj_i_1755007782839_404),
        .b(inj_b_1755007782840_428),
        .out_a(inj_out_a_1755007782840_485),
        .out_b(inj_out_b_1755007782840_518)
    );
    ModuleBasic ModuleBasic_inst_1755007782840_4515 (
        .out_a(inj_out_a_1755007782840_895),
        .out_b(inj_out_b_1755007782840_847),
        .a(inj_i_1755007782839_404),
        .b(inj_b_1755007782840_428)
    );
    always @* begin
        priority casex ({inj_case_expr_1755007782839_849, inj_case_inside_val_1755007782839_458[1:0]})
            4'b1???: inj_internal_out_1755007782839_746 = 24;
            4'b?1??: inj_internal_out_1755007782839_746 = 25;  
            4'b??1?: inj_internal_out_1755007782839_746 = 26;  
            4'b???1: inj_internal_out_1755007782839_746 = 27;  
            4'b0000: inj_internal_out_1755007782839_746 = 28;  
            default: inj_internal_out_1755007782839_746 = 29;
        endcase
    end
    // END: case_priority_casex_complex_mod_ts1755007782839

    assign inj_o_1755007782839_621 = inj_i_1755007782839_404; 
    // END: top_module_config_dummy_ts1755007782839

    PragmaOnceDirective PragmaOnceDirective_inst_1755007782839_3541 (
        .trigger_input(inj_trigger_input_1755007782839_881),
        .trigger_output(inj_trigger_output_1755007782839_345)
    );
endmodule

