interface struct_if;
    logic [7:0] packet_field1;
    logic [7:0] packet_field2;
    logic tx_en;
    modport Access (output packet_field1, output packet_field2, output tx_en);
endinterface
module CombinationalLogicImplicit (
    input logic [3:0] a,
    input logic [3:0] b,
    output logic [3:0] sum
);
    always @* begin
        sum = a + b;
    end
endmodule

module LintSeqNonBlockAssign (
    input logic clk,
    input logic in_f,
    output logic out_g
);
    always_ff @(posedge clk) begin
        out_g <= in_f;
    end
endmodule

module ModRegister (
    input logic din,
    output logic dout
);
    always @* begin
        dout = din;
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

module mod_default_disable (
    input bit enable_in,
    output bit out
);
    assign out = enable_in;
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

module mod_unused_ports (
    input wire unused_in,
    output logic unused_out
);
    assign unused_out = unused_in;
endmodule

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module split_multiple_in_branch (
    input logic clk_j,
    input logic condition_j,
    input logic [7:0] in_a_j,
    input logic [7:0] in_b_j,
    output logic [7:0] out_x_j,
    output logic [7:0] out_y_j
);
    always @(posedge clk_j) begin
        if (condition_j) begin
            out_x_j <= in_a_j * 3;
            out_y_j <= in_b_j + 1;
        end else begin
            out_x_j <= in_a_j;
            out_y_j <= in_b_j;
        end
    end
endmodule

module snippet #(
    parameter int SEL_PARAM = 5,
    parameter int SEL_PARAM = 6
) (
    input wire clk,
    input logic inj_b_1755007844463_443,
    input logic [3:0] inj_b_1755007844470_811,
    input logic inj_condition_j_1755007844458_171,
    input bit [7:0] inj_in1_1755007844457_840,
    input logic [2:0] inj_in_shift_1755007844457_745,
    input logic [7:0] inj_in_v_1755007844457_49,
    input int inj_in_val_1755007844459_346,
    input bit [7:0] inj_in_value_1755007844457_569,
    input bit inj_select_signal_1755007844459_410,
    input wire [63:0] inj_wide_a_1755007844466_861,
    input wire [63:0] inj_wide_b_1755007844466_220,
    input wire reset,
    output wire [127:0] inj_concat_out_1755007844466_684,
    output bit [7:0] inj_data_out_1755007844459_768,
    output logic [7:0] inj_data_out_1755007844460_313,
    output logic inj_data_out_1755007844461_568,
    output logic [7:0] inj_data_out_1755007844476_976,
    output logic inj_dout_1755007844469_76,
    output wire inj_o_c_1755007844465_345,
    output logic inj_o_out_1755007844471_681,
    output bit [7:0] inj_out1_1755007844457_273,
    output bit [7:0] inj_out2_1755007844457_326,
    output bit inj_out_1755007844462_341,
    output bit inj_out_1755007844474_750,
    output bit [2:0] inj_out_category_1755007844457_146,
    output logic inj_out_g_1755007844479_227,
    output logic [3:0] inj_out_part_1755007844457_176,
    output logic [7:0] inj_out_reg_1755007844457_332,
    output logic [7:0] inj_out_v_1755007844457_570,
    output int inj_out_val_1755007844459_507,
    output logic [7:0] inj_out_x_j_1755007844458_302,
    output logic [7:0] inj_out_y_j_1755007844458_929,
    output wire [7:0] inj_reduce_xor_out_1755007844466_454,
    output logic inj_reset_1755007844473_572,
    output logic inj_sum_1755007844463_841,
    output logic [3:0] inj_sum_1755007844470_581,
    output logic inj_tx_status_1755007844464_693,
    output logic inj_unused_out_1755007844458_868,
    output wire [63:0] inj_wide_sum_1755007844466_67
);
    // BEGIN: comb_simple_ts1755007844457
    // BEGIN: ModVectorAdd_ts1755007844457
    // BEGIN: module_assignments_in_loops_ts1755007844458
    localparam int PART_START = 4;
    localparam int PART_WIDTH = 4;
    logic [7:0] reg_var_ts1755007844458;
    logic [3:0] part_var_ts1755007844458;
        // BEGIN: SimpleLogicTest_ts1755007844459
        logic [7:0] temp_data_ts1755007844459;
            // BEGIN: ModuleHierarchy_Low_ts1755007844460
            ModuleBasic m1 (
                .a     (1'b1),
                .b     (inj_in_val_1755007844459_346),
                .out_a (),
                .out_b ( )
            );
            if (SEL_PARAM > 5) begin : gen_high
                int high_data_ts1755007844460;
                ModuleBasic m_high (
                    .a     (1'b0),
                    .b     (SEL_PARAM),
                    .out_a (),
                    .out_b (high_data_ts1755007844460)
                );
            end else begin : gen_low
                int low_data_ts1755007844460;
                ModuleBasic m_low (
                    .a     (1'b0),
                    .b     (SEL_PARAM),
                    .out_a (),
                    .out_b (low_data_ts1755007844460)
                );
            end
            for (genvar i = 0; i < 2; ++i) begin : gen_loop
                logic [1:0] sub_in_ts1755007844460;
                assign sub_in_ts1755007844460 = part_var_ts1755007844458[i*2 +: 2];
                int temp_int_ts1755007844460;
                    // BEGIN: module_simple_ts1755007844465
                    wire internal_xor_res_ts1755007844465;
                        // BEGIN: attributes_on_expr_port_ts1755007844471
                        logic internal_sig_ts1755007844471;
                            // BEGIN: cu_timeunit_mod_ts1755007844473
                            logic internal_sig_ts1755007844473;
                                // BEGIN: ModuleHierarchy_High_ts1755007844477
                                ModuleBasic m1 (
                                    .a      (1'b1),
                                    .b      (temp_int_ts1755007844460),
                                    .out_a  (),
                                    .out_b  ( )
                                );
                                if (SEL_PARAM > 5) begin : gen_high
                                    int high_data_ts1755007844476;
                                    ModuleBasic m_high (
                                        .a      (1'b0),
                                        .b      (SEL_PARAM),
                                        .out_a  (),
                                        .out_b  (high_data_ts1755007844476)
                                    );
                                end else begin : gen_low
                                    int low_data_ts1755007844476;
                                    ModuleBasic m_low (
                                        .a      (1'b0),
                                        .b      (SEL_PARAM),
                                        .out_a  (),
                                        .out_b  (low_data_ts1755007844476)
                                    );
                                end
                                for (genvar i = 0; i < 2; ++i) begin : gen_loop
                                    logic [1:0] sub_in_ts1755007844476;
                                    assign sub_in_ts1755007844476 = part_var_ts1755007844458[i*2 +: 2];
                                    int temp_int_ts1755007844476;
                                        LintSeqNonBlockAssign LintSeqNonBlockAssign_inst_1755007844479_291 (
                                            .clk(clk),
                                            .in_f(internal_sig_ts1755007844473),
                                            .out_g(inj_out_g_1755007844479_227)
                                        );
                                    ModuleBasic m_inst (
                                        .a      (1'b0),
                                        .b      (int'(sub_in_ts1755007844476)),
                                        .out_a  (),
                                        .out_b  (temp_int_ts1755007844476)
                                    );
                                    assign inj_data_out_1755007844476_976[i*4 +: 4] = temp_int_ts1755007844476[3:0];
                                end
                                // END: ModuleHierarchy_High_ts1755007844477

                                // BEGIN: mod_default_disable_ts1755007844475
                                assign inj_out_1755007844474_750 = inj_select_signal_1755007844459_410;
                                // END: mod_default_disable_ts1755007844475

                            always_ff @(posedge clk) begin
                                inj_reset_1755007844473_572 <= 1'b0;
                                internal_sig_ts1755007844473 = clk;
                            end
                            // END: cu_timeunit_mod_ts1755007844473

                        assign internal_sig_ts1755007844471 = inj_b_1755007844463_443 & inj_condition_j_1755007844458_171;
                        simple_adder sa_inst(
                            .a  (inj_b_1755007844463_443),
                            (* fanout_limit = 10 *) .b(inj_condition_j_1755007844458_171),
                            .sum(inj_o_out_1755007844471_681)
                        );
                        // END: attributes_on_expr_port_ts1755007844471

                        CombinationalLogicImplicit CombinationalLogicImplicit_inst_1755007844470_7100 (
                            .a(part_var_ts1755007844458),
                            .b(inj_b_1755007844470_811),
                            .sum(inj_sum_1755007844470_581)
                        );
                        ModRegister ModRegister_inst_1755007844469_3016 (
                            .dout(inj_dout_1755007844469_76),
                            .din(inj_condition_j_1755007844458_171)
                        );
                        // BEGIN: wide_bus_ops_ts1755007844467
                        assign inj_wide_sum_1755007844466_67 = inj_wide_a_1755007844466_861 + inj_wide_b_1755007844466_220;
                        assign inj_reduce_xor_out_1755007844466_454 = ^inj_wide_a_1755007844466_861[63:0];
                        assign inj_concat_out_1755007844466_684 = {inj_wide_a_1755007844466_861, inj_wide_b_1755007844466_220};
                        // END: wide_bus_ops_ts1755007844467

                    assign internal_xor_res_ts1755007844465 = clk ^ reset;
                    assign inj_o_c_1755007844465_345 = internal_xor_res_ts1755007844465 & clk;
                    // END: module_simple_ts1755007844465

                    // BEGIN: module_struct_write_ts1755007844464
                    struct_if stif_inst();
                    always_comb begin
                        stif_inst.packet_field1 = reg_var_ts1755007844458;
                        stif_inst.packet_field2 = inj_in_v_1755007844457_49;
                        stif_inst.tx_en = 1'b1;
                        inj_tx_status_1755007844464_693 = stif_inst.tx_en;
                    end
                    // END: module_struct_write_ts1755007844464

                    // BEGIN: simple_adder_ts1755007844463
                    assign inj_sum_1755007844463_841 = inj_condition_j_1755007844458_171 + inj_b_1755007844463_443;
                    // END: simple_adder_ts1755007844463

                    mod_default_disable mod_default_disable_inst_1755007844462_846 (
                        .enable_in(inj_select_signal_1755007844459_410),
                        .out(inj_out_1755007844462_341)
                    );
                    // BEGIN: child_scalar_port_ts1755007844461
                    assign inj_data_out_1755007844461_568 = inj_condition_j_1755007844458_171;
                    // END: child_scalar_port_ts1755007844461

                ModuleBasic m_inst (
                    .a      (1'b0),
                    .b      (int'(sub_in_ts1755007844460)),
                    .out_a  (),
                    .out_b  (temp_int_ts1755007844460)
                );
                assign inj_data_out_1755007844460_313[i*4 +: 4] = temp_int_ts1755007844460[3:0];
            end
            // END: ModuleHierarchy_Low_ts1755007844460

        always_comb begin
            if (inj_select_signal_1755007844459_410) begin
                temp_data_ts1755007844459 = inj_in_value_1755007844457_569 + 1;
            end else begin
                temp_data_ts1755007844459 = inj_in_value_1755007844457_569 - 1;
            end
            inj_data_out_1755007844459_768 = temp_data_ts1755007844459;
        end
        // END: SimpleLogicTest_ts1755007844459

        // BEGIN: undeclared_but_found_pkg_diag_mod_ts1755007844459
        assign inj_out_val_1755007844459_507 = inj_in_val_1755007844459_346;
        // END: undeclared_but_found_pkg_diag_mod_ts1755007844459

        mod_unused_ports mod_unused_ports_inst_1755007844458_4821 (
            .unused_in(reset),
            .unused_out(inj_unused_out_1755007844458_868)
        );
        split_multiple_in_branch split_multiple_in_branch_inst_1755007844458_6426 (
            .condition_j(inj_condition_j_1755007844458_171),
            .in_a_j(inj_in_v_1755007844457_49),
            .in_b_j(reg_var_ts1755007844458),
            .out_x_j(inj_out_x_j_1755007844458_302),
            .out_y_j(inj_out_y_j_1755007844458_929),
            .clk_j(clk)
        );
    always_comb begin
        reg_var_ts1755007844458  = inj_in_v_1755007844457_49;
        part_var_ts1755007844458 = 4'h0;
        for (int i = 0; i < 4; i++) begin
            reg_var_ts1755007844458  = reg_var_ts1755007844458 + i;
            reg_var_ts1755007844458 += (i * 2);
            reg_var_ts1755007844458 <<= inj_in_shift_1755007844457_745;
            reg_var_ts1755007844458[i % 8] = (reg_var_ts1755007844458[i % 8] == 1'b0);
            reg_var_ts1755007844458[PART_START +: PART_WIDTH] = i[3:0];
        end
        part_var_ts1755007844458 = reg_var_ts1755007844458[7:4];
    end
    assign inj_out_reg_1755007844457_332  = reg_var_ts1755007844458;
    assign inj_out_part_1755007844457_176 = part_var_ts1755007844458;
    // END: module_assignments_in_loops_ts1755007844458

    assign inj_out_v_1755007844457_570 = inj_in_v_1755007844457_49 + 8'h01;
    // END: ModVectorAdd_ts1755007844457

    always @* begin
        inj_out1_1755007844457_273 = inj_in1_1755007844457_840 & inj_in_value_1755007844457_569;
        inj_out2_1755007844457_326 = inj_in1_1755007844457_840 | inj_in_value_1755007844457_569;
    end
    // END: comb_simple_ts1755007844457

    mod_if_elseif_chained mod_if_elseif_chained_inst_1755007844457_3972 (
        .in_value(inj_in_value_1755007844457_569),
        .out_category(inj_out_category_1755007844457_146)
    );
endmodule

