interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module bitwise_ops (
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [7:0] in3,
    output logic [7:0] out
);
    assign out = (in1 & in2) | (~in3) ^ (in1 << 2) >> 1;
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

module split_arith_blocking (
    input logic [7:0] op1_u,
    input logic [7:0] op2_u,
    output logic [7:0] diff_u,
    output logic [7:0] prod_u,
    output logic [7:0] sum_u
);
    always @(*) begin
        sum_u = op1_u + op2_u;
        diff_u = op1_u - op2_u;
        prod_u = op1_u * op2_u;
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
    input wire [2:0] inj_count_in_1755004214608_38,
    input logic inj_data_value_1755004214601_650,
    input int inj_i_val_1755004214600_531,
    input logic [7:0] inj_in3_1755004214602_553,
    input logic [7:0] inj_in_1755004214600_757,
    input wire [7:0] inj_in_func_a_1755004214614_550,
    input wire [7:0] inj_in_func_b_1755004214614_111,
    input logic inj_level1_en_1755004214601_650,
    input logic inj_level2_en_1755004214601_79,
    input logic [7:0] inj_op2_u_1755004214601_833,
    input logic [2:0] inj_shamt_1755004214607_492,
    input wire reset,
    output wire [2:0] inj_count_out_1755004214608_945,
    output logic [7:0] inj_diff_u_1755004214601_490,
    output logic [7:0] inj_left_shift_1755004214607_769,
    output logic inj_nm_out_1755004214612_20,
    output int inj_o_val_1755004214600_960,
    output logic [7:0] inj_out_1755004214600_611,
    output logic [7:0] inj_out_1755004214602_26,
    output logic [7:0] inj_out_func_result_1755004214614_781,
    output logic inj_out_pd_1755004214600_99,
    output logic [7:0] inj_out_val_1755004214605_592,
    output logic inj_out_valid_status_1755004214603_766,
    output logic [7:0] inj_out_vec_1755004214604_129,
    output logic [7:0] inj_prod_u_1755004214601_56,
    output logic [7:0] inj_result_and_1755004214610_646,
    output logic [7:0] inj_result_or_1755004214610_357,
    output logic inj_result_out_1755004214601_831,
    output logic [7:0] inj_result_xor_1755004214610_157,
    output logic [7:0] inj_right_shift_arith_1755004214607_744,
    output logic [7:0] inj_right_shift_logic_1755004214607_34,
    output logic [7:0] inj_sum_u_1755004214601_386
);
    // BEGIN: ProgramDefinition_ts1755004214600
    // BEGIN: mod_automatic_task_ts1755004214601
    task automatic update_val(input int in_v, output int out_v);
        out_v = in_v * 2;
    endtask
    always_comb begin
        int temp_val_ts1755004214600;
            // BEGIN: simple_seq_ts1755004214608
            reg [2:0] counter_reg_ts1755004214608;
                // BEGIN: module_function_ts1755004214614
                function automatic [7:0] add_and_subtract;
                input [7:0] val1;
                input [7:0] val2;
                reg [7:0] temp_ts1755004214614;
                begin
                temp_ts1755004214614 = val1 + val2;
                add_and_subtract = temp_ts1755004214614 - 1;
                end
                endfunction
                always_comb begin
                inj_out_func_result_1755004214614_781 = add_and_subtract(inj_in_func_a_1755004214614_550, inj_in_func_b_1755004214614_111);
                end
                // END: module_function_ts1755004214614

                // BEGIN: nested_module_ts1755004214612
                assign inj_nm_out_1755004214612_20 = inj_level2_en_1755004214601_79;
                // END: nested_module_ts1755004214612

                // BEGIN: BitwiseOperations_ts1755004214610
                assign inj_result_and_1755004214610_646 = inj_op2_u_1755004214601_833 & inj_in_1755004214600_757;
                assign inj_result_or_1755004214610_357 = inj_op2_u_1755004214601_833 | inj_in3_1755004214602_553;
                assign inj_result_xor_1755004214610_157 = inj_in_1755004214600_757 ^ inj_in3_1755004214602_553;
                // END: BitwiseOperations_ts1755004214610

            always @(posedge clk or posedge reset) begin
                if (reset) begin
                    counter_reg_ts1755004214608 <= 3'b000;
                end else begin
                    counter_reg_ts1755004214608 <= inj_count_in_1755004214608_38 + 3'b001;
                end
            end
            assign inj_count_out_1755004214608_945 = counter_reg_ts1755004214608;
            // END: simple_seq_ts1755004214608

            shift_ops shift_ops_inst_1755004214607_5749 (
                .data(inj_in_1755004214600_757),
                .shamt(inj_shamt_1755004214607_492),
                .left_shift(inj_left_shift_1755004214607_769),
                .right_shift_arith(inj_right_shift_arith_1755004214607_744),
                .right_shift_logic(inj_right_shift_logic_1755004214607_34)
            );
            // BEGIN: used_before_declared_diag_mod_ts1755004214605
            logic [7:0] undeclared_var_ubddm = 8'd5;
            assign inj_out_val_1755004214605_592 = inj_in_1755004214600_757 + undeclared_var_ubddm;
            // END: used_before_declared_diag_mod_ts1755004214605

            // BEGIN: SimpleLoopExample_ts1755004214604
            always_comb begin
                for (int i = 0; i < 8; i++) begin
                    inj_out_vec_1755004214604_129[i] = inj_in3_1755004214602_553[7 - i];
                end
            end
            // END: SimpleLoopExample_ts1755004214604

            // BEGIN: module_assign_blocking_ts1755004214603
            my_if vif_inst();
            always_comb begin
                vif_inst.data = inj_in_1755004214600_757;
                vif_inst.valid = 1'b1;
                vif_inst.ready = 1'b0;
                inj_out_valid_status_1755004214603_766 = vif_inst.valid;
            end
            // END: module_assign_blocking_ts1755004214603

            bitwise_ops bitwise_ops_inst_1755004214602_900 (
                .in1(inj_op2_u_1755004214601_833),
                .in2(inj_in_1755004214600_757),
                .in3(inj_in3_1755004214602_553),
                .out(inj_out_1755004214602_26)
            );
            split_arith_blocking split_arith_blocking_inst_1755004214601_153 (
                .diff_u(inj_diff_u_1755004214601_490),
                .prod_u(inj_prod_u_1755004214601_56),
                .sum_u(inj_sum_u_1755004214601_386),
                .op1_u(inj_in_1755004214600_757),
                .op2_u(inj_op2_u_1755004214601_833)
            );
            // BEGIN: nested_blocks_ts1755004214601
            always_comb begin : main_block 
                inj_result_out_1755004214601_831 = 1'b0; 
                if (inj_level1_en_1755004214601_650) begin : inner_block1 
                    if (inj_level2_en_1755004214601_79) begin : inner_block2 
                        inj_result_out_1755004214601_831 = inj_data_value_1755004214601_650;
                    end 
                end 
            end
            // END: nested_blocks_ts1755004214601

        update_val(inj_i_val_1755004214600_531, temp_val_ts1755004214600);
        inj_o_val_1755004214600_960 = temp_val_ts1755004214600;
    end
    // END: mod_automatic_task_ts1755004214601

    sub_inst_array_mod sub_inst_array_mod_inst_1755004214600_6164 (
        .in(inj_in_1755004214600_757),
        .out(inj_out_1755004214600_611)
    );
    assign inj_out_pd_1755004214600_99 = reset;
    // END: ProgramDefinition_ts1755004214600
endmodule

