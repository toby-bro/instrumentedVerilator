interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module mod_fixup_target (
    input logic fs_in_target,
    output logic fs_out_target
);
    assign fs_out_target = fs_in_target;
endmodule

module module_latch (
    input wire [7:0] in_latch_data,
    input wire in_latch_en,
    output reg [7:0] out_latch_reg
);
    always_latch begin
    if (in_latch_en) begin
        out_latch_reg = in_latch_data;
    end
    end
endmodule

module module_task_args (
    input logic [7:0] arg_in_task,
    input logic [7:0] data_a_init_task,
    input logic start_task,
    output logic [7:0] data_a_out_task,
    output logic [7:0] data_b_out_task
);
    logic [7:0] data_a ;
    logic [7:0] data_b ;
    task automatic modify_vars;
        input logic [7:0] task_arg;
        logic [7:0] task_local ;
        begin
            task_local = task_arg;
            data_a = task_local + 8'd1;
            data_b = task_arg - 8'd1;
        end
    endtask
    always_comb begin
        if (start_task) begin
            data_a = data_a_init_task;
            data_b = 8'hFF;
            modify_vars(arg_in_task);
        end else begin
            data_a = 8'h00;
            data_b = 8'h00;
        end
    end
    always_comb begin
        data_a_out_task = data_a + 8'd2;
        data_b_out_task = data_b;
    end
endmodule

module shift_ops (
    input logic [7:0] data,
    input logic [2:0] shamt,
    output logic [7:0] left_shift,
    output logic [7:0] right_shift_arith,
    output logic [7:0] right_shift_logic
);
    assign left_shift = data << shamt;
    assign right_shift_logic = data >> shamt;
    assign right_shift_arith = data >>> shamt;
endmodule

module split_basic_nonblocking (
    input logic clk_b,
    input logic [7:0] in2_a,
    output logic [7:0] out2_a
);
    always @(posedge clk_b) begin
        out2_a <= in2_a;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_bind_in_1755007779093_871,
    input logic [7:0] inj_d1_1755007779094_957,
    input logic [7:0] inj_d2_1755007779094_511,
    input logic [7:0] inj_d3_1755007779094_675,
    input logic [7:0] inj_data3_1755007779098_695,
    input logic [3:0] inj_flags_1755007779094_28,
    input logic [15:0] inj_in_data_1755007779110_5,
    input logic [3:0] inj_in_l_1755007779104_740,
    input logic [1:0] inj_sel_code_1755007779098_740,
    input logic [2:0] inj_shamt_1755007779097_718,
    input wire reset,
    output logic inj_bind_out_1755007779093_970,
    output logic [7:0] inj_data_a_out_task_1755007779101_343,
    output logic [7:0] inj_data_b_out_task_1755007779101_677,
    output logic inj_dummy_out_1755007779126_220,
    output logic inj_fs_out_target_1755007779100_71,
    output logic [7:0] inj_left_shift_1755007779097_303,
    output wire inj_loop_out_1755007779102_477,
    output logic [7:0] inj_out1_1755007779094_423,
    output logic [7:0] inj_out2_a_1755007779106_350,
    output logic [7:0] inj_out_1755007779104_568,
    output logic [7:0] inj_out_data_1755007779126_592,
    output logic [7:0] inj_out_field_a_1755007779110_274,
    output logic [7:0] inj_out_field_b_1755007779110_794,
    output reg [7:0] inj_out_latch_reg_1755007779117_725,
    output logic inj_out_valid_1755007779126_10,
    output logic inj_out_valid_status_1755007779107_856,
    output wire inj_p_out_1755007779122_998,
    output logic inj_q_1755007779093_590,
    output logic [7:0] inj_res_1755007779112_128,
    output logic [7:0] inj_right_shift_arith_1755007779097_795,
    output logic [7:0] inj_right_shift_logic_1755007779097_413,
    output logic [7:0] inj_selected_data_1755007779098_550
);
    // BEGIN: bind_module_ts1755007779093
    // BEGIN: ModClockedResetReg_ts1755007779094
    // BEGIN: dup_logic_ops_ts1755007779096
    logic cond1_ts1755007779096, cond2_ts1755007779096, cond3_ts1755007779096;
    logic complex_cond1_ts1755007779096, complex_cond2_ts1755007779096;
        // BEGIN: Comb_Loop_ts1755007779102
        wire loop_wire1_ts1755007779102;
        wire loop_wire2_ts1755007779102;
            // BEGIN: coalesced_assign_ts1755007779104
            wire [7:0] temp_wire_ts1755007779104;
                // BEGIN: explicit_non_ansi_decl_module_ts1755007779122
                input logic complex_cond1_ts1755007779096_ts1755007779122;
                output wire inj_p_out_1755007779122_998_ts1755007779122;
                    // BEGIN: virtual_interface_lookup_mod_ts1755007779126
                    always_comb begin
                        inj_out_data_1755007779126_592  = inj_d1_1755007779094_957;
                        inj_out_valid_1755007779126_10 = complex_cond2_ts1755007779096;
                        inj_dummy_out_1755007779126_220 = cond3_ts1755007779096;
                    end
                    // END: virtual_interface_lookup_mod_ts1755007779126

                assign inj_p_out_1755007779122_998_ts1755007779122 = complex_cond1_ts1755007779096_ts1755007779122;
                // END: explicit_non_ansi_decl_module_ts1755007779122

                module_latch module_latch_inst_1755007779117_774 (
                    .in_latch_data(temp_wire_ts1755007779104),
                    .in_latch_en(clk),
                    .out_latch_reg(inj_out_latch_reg_1755007779117_725)
                );
                // BEGIN: dup_nested_if_ts1755007779113
                always_comb begin
                    inj_res_1755007779112_128 = '0;
                    if (inj_shamt_1755007779097_718 == 3'b001) begin
                        if (inj_d1_1755007779094_957 > inj_d2_1755007779094_511) begin
                            inj_res_1755007779112_128 = inj_d1_1755007779094_957 + inj_d2_1755007779094_511;
                        end else begin
                            inj_res_1755007779112_128 = inj_d1_1755007779094_957 - inj_d2_1755007779094_511;
                        end
                    end else if (inj_shamt_1755007779097_718 == 3'b010) begin
                        if (inj_d1_1755007779094_957 > inj_d2_1755007779094_511) begin
                            inj_res_1755007779112_128 = inj_d1_1755007779094_957 + inj_d2_1755007779094_511;
                        end else begin
                            inj_res_1755007779112_128 = inj_d1_1755007779094_957 - inj_d2_1755007779094_511;
                        end
                    end else if (inj_shamt_1755007779097_718 == 3'b011) begin
                        if (inj_d1_1755007779094_957 < inj_d2_1755007779094_511) begin
                            inj_res_1755007779112_128 = inj_d1_1755007779094_957 * inj_d2_1755007779094_511;
                        end else begin
                            inj_res_1755007779112_128 = inj_d1_1755007779094_957 / ((inj_d2_1755007779094_511 == 0) ? 1 : inj_d2_1755007779094_511);
                        end
                    end else if (inj_shamt_1755007779097_718 == 3'b100) begin
                        if (inj_d1_1755007779094_957 != inj_d2_1755007779094_511) begin
                            if (inj_d1_1755007779094_957 > inj_d2_1755007779094_511) inj_res_1755007779112_128 = inj_d1_1755007779094_957;
                            else inj_res_1755007779112_128 = inj_d2_1755007779094_511;
                        end else begin
                            inj_res_1755007779112_128 = inj_d1_1755007779094_957 + inj_d2_1755007779094_511;
                        end
                    end
                    else begin
                        inj_res_1755007779112_128 = inj_d1_1755007779094_957 ^ inj_d2_1755007779094_511;
                    end
                end
                // END: dup_nested_if_ts1755007779113

                // BEGIN: StructExample_ts1755007779110
                typedef struct packed {
                    logic [7:0] field_a_ts1755007779110;
                    logic [7:0] field_b_ts1755007779110;
                } example_struct_t;
                example_struct_t my_struct;
                always_comb begin
                    my_struct     = inj_in_data_1755007779110_5;
                    inj_out_field_a_1755007779110_274   = my_struct.field_a_ts1755007779110;
                    inj_out_field_b_1755007779110_794   = my_struct.field_b_ts1755007779110;
                end
                // END: StructExample_ts1755007779110

                // BEGIN: module_assign_blocking_ts1755007779108
                my_if vif_inst();
                always_comb begin
                    vif_inst.data = inj_d3_1755007779094_675;
                    vif_inst.valid = 1'b1;
                    vif_inst.ready = 1'b0;
                    inj_out_valid_status_1755007779107_856 = vif_inst.valid;
                end
                // END: module_assign_blocking_ts1755007779108

                split_basic_nonblocking split_basic_nonblocking_inst_1755007779106_8048 (
                    .in2_a(inj_d1_1755007779094_957),
                    .out2_a(inj_out2_a_1755007779106_350),
                    .clk_b(clk)
                );
            assign temp_wire_ts1755007779104[7:4] = inj_flags_1755007779094_28;
            assign temp_wire_ts1755007779104[3:0] = inj_in_l_1755007779104_740;
            assign inj_out_1755007779104_568 = temp_wire_ts1755007779104;
            // END: coalesced_assign_ts1755007779104

        assign loop_wire1_ts1755007779102 = loop_wire2_ts1755007779102 | clk;
        assign loop_wire2_ts1755007779102 = loop_wire1_ts1755007779102; 
        assign inj_loop_out_1755007779102_477 = loop_wire1_ts1755007779102;
        // END: Comb_Loop_ts1755007779102

        module_task_args module_task_args_inst_1755007779101_9502 (
            .arg_in_task(inj_data3_1755007779098_695),
            .data_a_init_task(inj_d1_1755007779094_957),
            .start_task(complex_cond2_ts1755007779096),
            .data_a_out_task(inj_data_a_out_task_1755007779101_343),
            .data_b_out_task(inj_data_b_out_task_1755007779101_677)
        );
        mod_fixup_target mod_fixup_target_inst_1755007779100_2597 (
            .fs_in_target(cond2_ts1755007779096),
            .fs_out_target(inj_fs_out_target_1755007779100_71)
        );
        // BEGIN: IfElseIfChain_ts1755007779098
        always_comb begin
            if (inj_sel_code_1755007779098_740 == 2'b00) begin
                inj_selected_data_1755007779098_550 = inj_d2_1755007779094_511;
            end else if (inj_sel_code_1755007779098_740 == 2'b01) begin
                inj_selected_data_1755007779098_550 = inj_d1_1755007779094_957;
            end else if (inj_sel_code_1755007779098_740 == 2'b10) begin
                inj_selected_data_1755007779098_550 = inj_d3_1755007779094_675;
            end else begin
                inj_selected_data_1755007779098_550 = inj_data3_1755007779098_695;
            end
        end
        // END: IfElseIfChain_ts1755007779098

        shift_ops shift_ops_inst_1755007779097_6977 (
            .shamt(inj_shamt_1755007779097_718),
            .left_shift(inj_left_shift_1755007779097_303),
            .right_shift_arith(inj_right_shift_arith_1755007779097_795),
            .right_shift_logic(inj_right_shift_logic_1755007779097_413),
            .data(inj_d2_1755007779094_511)
        );
    assign cond1_ts1755007779096 = inj_flags_1755007779094_28[0] && inj_flags_1755007779094_28[1];
    assign cond2_ts1755007779096 = inj_flags_1755007779094_28[2] || inj_flags_1755007779094_28[3];
    assign cond3_ts1755007779096 = !inj_flags_1755007779094_28[0];
    assign complex_cond1_ts1755007779096 = (cond1_ts1755007779096 || cond2_ts1755007779096) && cond3_ts1755007779096;
    assign complex_cond2_ts1755007779096 = !(inj_flags_1755007779094_28[0] && inj_flags_1755007779094_28[1]) || (inj_flags_1755007779094_28[2] || !inj_flags_1755007779094_28[3]);
    always_comb begin
        inj_out1_1755007779094_423 = '0;
        if (complex_cond1_ts1755007779096) begin
            inj_out1_1755007779094_423 = inj_d1_1755007779094_957 + inj_d2_1755007779094_511;
        end else begin
            inj_out1_1755007779094_423 = inj_d1_1755007779094_957 ^ inj_d3_1755007779094_675;
        end
        if (complex_cond2_ts1755007779096) begin
            inj_out1_1755007779094_423 = inj_out1_1755007779094_423 + inj_d3_1755007779094_675;
        end else begin
            inj_out1_1755007779094_423 = inj_out1_1755007779094_423 - inj_d3_1755007779094_675;
        end
        if ((inj_flags_1755007779094_28[0] && inj_flags_1755007779094_28[1]) && (!inj_flags_1755007779094_28[2] || inj_flags_1755007779094_28[3])) begin
            inj_out1_1755007779094_423 = inj_out1_1755007779094_423 * 2;
        end
    end
    // END: dup_logic_ops_ts1755007779096

    always @(posedge clk or negedge reset) begin
    if (!reset) begin
        inj_q_1755007779093_590 <= 1'b0;
    end else begin
        inj_q_1755007779093_590 <= inj_bind_in_1755007779093_871;
    end
    end
    // END: ModClockedResetReg_ts1755007779094

    assign inj_bind_out_1755007779093_970 = inj_bind_in_1755007779093_871;
    // END: bind_module_ts1755007779093
endmodule

