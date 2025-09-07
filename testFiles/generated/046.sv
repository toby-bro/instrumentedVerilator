interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module ModSimpleLogic (
    input logic a,
    input logic b,
    output logic y
);
    assign y = a ^ b;
endmodule

module SignedUnsignedConversions (
    input integer in_int,
    input logic [31:0] in_l32,
    input logic signed [7:0] in_s8,
    input logic [15:0] in_u16,
    output logic signed [15:0] out_s16,
    output logic signed [31:0] out_s32_from_int,
    output logic signed [31:0] out_s32_from_l32,
    output logic [31:0] out_u32_from_int,
    output logic [31:0] out_u32_from_l32,
    output logic [7:0] out_u8
);
    always_comb begin
        out_u8 = $unsigned(in_s8);
        out_s16 = $signed(in_u16);
        out_s32_from_l32 = $signed(in_l32);
        out_u32_from_l32 = $unsigned(in_l32);
        out_s32_from_int = $signed(in_int);
        out_u32_from_int = $unsigned(in_int);
    end
endmodule

module SynchronousMemory (
    input logic clk,
    input logic [4:0] read_address,
    input logic rst,
    input logic [4:0] write_address,
    input logic [7:0] write_data,
    input logic write_en,
    output logic [7:0] read_data
);
    logic [7:0] mem [0:31];
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            read_data <= 8'h0;
        end else begin
            if (write_en) begin
                mem[write_address] <= write_data;
            end
            read_data <= mem[read_address];
        end
    end
endmodule

module func_macro_args (
    input int input_int,
    output int output_int
);
    `define ADD(a, b)       ((a) + (b))
    `define SUBTRACT(x, y)  ((x) - (y))
    localparam int P1_ADD = `ADD(10, 20);
    int p2_sub_var;
    always_comb begin
        p2_sub_var = `SUBTRACT(50, input_int);
    end
    assign output_int = P1_ADD + p2_sub_var;
endmodule

module mod_fixup_target (
    input logic fs_in_target,
    output logic fs_out_target
);
    assign fs_out_target = fs_in_target;
endmodule

module mod_fixup_syntax_user (
    input logic fs_in,
    output wire fs_out
);
    logic fixup_out_val;
    mod_fixup_target fixup_inst (
        .fs_in_target(fs_in),
        .fs_out_target(fixup_out_val)
    );
    assign fs_out = fixup_out_val;
endmodule

module mod_split_case (
    input logic [7:0] data_in,
    input logic [1:0] sel,
    output logic [7:0] out_case_a,
    output logic [7:0] out_case_b
);
    logic [7:0]  split_case_var;
    logic [7:0] other_case_var;
    always_comb begin
        split_case_var = 8'hFF;
        other_case_var = 8'hAA;
        case (sel)
            2'b00: begin
                split_case_var = data_in + 5;
                other_case_var = data_in + 6;
            end
            2'b01: begin
                split_case_var = data_in - 5;
                other_case_var = data_in - 6;
            end
            default: begin
                split_case_var = data_in;
                other_case_var = data_in;
            end
        endcase
        out_case_a = split_case_var;
        out_case_b = other_case_var;
    end
endmodule

module split_single_stmt (
    input logic [7:0] in_q,
    output logic [7:0] out_q
);
    always @(*) begin
        out_q = in_q + 1;
    end
endmodule

module typedef_union_mod (
    input logic [15:0] packed_in,
    output logic [7:0] field0_byte_o
);
    typedef union packed {
        logic [15:0] word;
        logic [1:0][7:0] byte_fields;
    } my_packed_union_t;
    my_packed_union_t my_union_var;
    always_comb begin
        my_union_var.word = packed_in;
    end
    assign field0_byte_o = my_union_var.byte_fields[0];
endmodule

module variable_sel_mux (
    input logic [7:0] in,
    input logic [2:0] index,
    output logic out
);
    assign out = in[index];
endmodule

module snippet #(
    parameter int P_PORT_VAL = 25
) (
    input wire clk,
    input logic inj_a_1755007766619_369,
    input int inj_b_1755007766619_530,
    input logic [7:0] inj_data_case_a_1755007766618_718,
    input logic [7:0] inj_data_case_b_1755007766618_205,
    input logic [7:0] inj_in3_1755007766636_95,
    input logic [3:0] inj_in_h_1755007766634_835,
    input wire [2:0] inj_in_index_1755007766622_729,
    input integer inj_in_int_1755007766649_449,
    input logic [31:0] inj_in_l32_1755007766649_548,
    input logic [3:0] inj_in_l_1755007766634_157,
    input wire [1:0] inj_in_part_lsb_1755007766622_900,
    input logic [15:0] inj_in_u16_1755007766649_716,
    input wire [7:0] inj_in_vector_1755007766622_582,
    input logic [2:0] inj_index_1755007766621_160,
    input logic [4:0] inj_read_address_1755007766626_447,
    input bit inj_select_a_1755007766674_25,
    input logic [1:0] inj_select_case_1755007766618_511,
    input logic [4:0] inj_write_address_1755007766626_863,
    input wire reset,
    output logic inj_case_output_ready_1755007766618_199,
    output int inj_config_data_out_1755007766628_137,
    output wire inj_data_d_1755007766617_205,
    output logic [7:0] inj_data_out_1755007766632_283,
    output logic inj_dummy_out_1755007766623_705,
    output logic [7:0] inj_field0_byte_o_1755007766665_103,
    output logic [7:0] inj_field2_o_1755007766653_601,
    output wire inj_fs_out_1755007766658_980,
    output logic inj_fs_out_target_1755007766679_955,
    output logic inj_is_even_1755007766684_574,
    output logic inj_nand_out_1755007766636_680,
    output logic inj_nor_out_1755007766636_811,
    output logic [7:0] inj_o_sum_1755007766643_407,
    output logic [7:0] inj_out1_1755007766668_878,
    output logic inj_out_1755007766621_853,
    output logic [7:0] inj_out_1755007766634_580,
    output logic inj_out_1755007766639_577,
    output logic [7:0] inj_out_1755007766641_654,
    output logic inj_out_a_1755007766619_132,
    output int inj_out_b_1755007766619_737,
    output logic inj_out_bit_select_1755007766622_668,
    output logic [7:0] inj_out_bitwise_ops_1755007766622_464,
    output logic [7:0] inj_out_case_a_1755007766619_719,
    output logic [7:0] inj_out_case_b_1755007766619_127,
    output logic [7:0] inj_out_data_1755007766623_699,
    output logic [3:0] inj_out_part_select_1755007766622_380,
    output logic [7:0] inj_out_q_1755007766646_714,
    output logic signed [15:0] inj_out_s16_1755007766649_176,
    output logic signed [31:0] inj_out_s32_from_int_1755007766649_11,
    output logic signed [31:0] inj_out_s32_from_l32_1755007766649_282,
    output logic [31:0] inj_out_u32_from_int_1755007766649_582,
    output logic [31:0] inj_out_u32_from_l32_1755007766649_681,
    output logic [7:0] inj_out_u8_1755007766649_918,
    output logic [31:0] inj_out_val_1755007766674_977,
    output int inj_out_val_1755007766691_510,
    output logic inj_out_valid_1755007766623_2,
    output logic [7:0] inj_out_vector_assign_1755007766622_176,
    output int inj_output_int_1755007766630_252,
    output logic [7:0] inj_read_data_1755007766626_243,
    output logic inj_xnor_out_1755007766636_189,
    output logic inj_y_1755007766661_650
);
    // BEGIN: simple_logic_b_ts1755007766618
    // BEGIN: module_case_write_ts1755007766618
    // BEGIN: ModuleBasic_ts1755007766620
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c_ts1755007766620;
    int   d_ts1755007766620;
    always_comb begin
        logic temp_v_ts1755007766620;
            // BEGIN: coalesced_assign_ts1755007766634
            wire [7:0] temp_wire_ts1755007766634;
                // BEGIN: dup_logic_ops_ts1755007766670
                logic cond1_ts1755007766669, cond2_ts1755007766669, cond3_ts1755007766669;
                logic complex_cond1_ts1755007766669, complex_cond2_ts1755007766669;
                    // BEGIN: module_in_program_ref_ts1755007766692
                    assign inj_out_val_1755007766691_510 = inj_b_1755007766619_530;
                    // END: module_in_program_ref_ts1755007766692

                    // BEGIN: FunctionTaskMod_ts1755007766685
                    function automatic bit check_even(input logic [7:0] v);
                        check_even = ~v[0];
                    endfunction
                    task automatic dummy_task(input logic [7:0] v);
                        int tmp_ts1755007766685;
                        tmp_ts1755007766685 = v;
                    endtask
                    assign inj_is_even_1755007766684_574 = check_even(inj_data_case_b_1755007766618_205);
                    // END: FunctionTaskMod_ts1755007766685

                    mod_fixup_target mod_fixup_target_inst_1755007766679_7396 (
                        .fs_out_target(inj_fs_out_target_1755007766679_955),
                        .fs_in_target(cond2_ts1755007766669)
                    );
                    // BEGIN: member_access_packed_union_ts1755007766674
                    typedef union packed {
                        logic [31:0] a_ts1755007766674; 
                        logic [31:0] b_ts1755007766674; 
                    } my_packed_union;
                    my_packed_union union_var;
                    always_comb begin
                        if (inj_select_a_1755007766674_25)
                            union_var.a_ts1755007766674 = inj_in_l32_1755007766649_548;
                        else
                            union_var.b_ts1755007766674 = inj_in_l32_1755007766649_548[31:0];
                        inj_out_val_1755007766674_977 = union_var.a_ts1755007766674;
                    end
                    // END: member_access_packed_union_ts1755007766674

                assign cond1_ts1755007766669 = inj_in_h_1755007766634_835[0] && inj_in_h_1755007766634_835[1];
                assign cond2_ts1755007766669 = inj_in_h_1755007766634_835[2] || inj_in_h_1755007766634_835[3];
                assign cond3_ts1755007766669 = !inj_in_h_1755007766634_835[0];
                assign complex_cond1_ts1755007766669 = (cond1_ts1755007766669 || cond2_ts1755007766669) && cond3_ts1755007766669;
                assign complex_cond2_ts1755007766669 = !(inj_in_h_1755007766634_835[0] && inj_in_h_1755007766634_835[1]) || (inj_in_h_1755007766634_835[2] || !inj_in_h_1755007766634_835[3]);
                always_comb begin
                    inj_out1_1755007766668_878 = '0;
                    if (complex_cond1_ts1755007766669) begin
                        inj_out1_1755007766668_878 = inj_data_case_a_1755007766618_718 + inj_data_case_b_1755007766618_205;
                    end else begin
                        inj_out1_1755007766668_878 = inj_data_case_a_1755007766618_718 ^ inj_in3_1755007766636_95;
                    end
                    if (complex_cond2_ts1755007766669) begin
                        inj_out1_1755007766668_878 = inj_out1_1755007766668_878 + inj_in3_1755007766636_95;
                    end else begin
                        inj_out1_1755007766668_878 = inj_out1_1755007766668_878 - inj_in3_1755007766636_95;
                    end
                    if ((inj_in_h_1755007766634_835[0] && inj_in_h_1755007766634_835[1]) && (!inj_in_h_1755007766634_835[2] || inj_in_h_1755007766634_835[3])) begin
                        inj_out1_1755007766668_878 = inj_out1_1755007766668_878 * 2;
                    end
                end
                // END: dup_logic_ops_ts1755007766670

                typedef_union_mod typedef_union_mod_inst_1755007766665_6261 (
                    .packed_in(inj_in_u16_1755007766649_716),
                    .field0_byte_o(inj_field0_byte_o_1755007766665_103)
                );
                ModSimpleLogic ModSimpleLogic_inst_1755007766661_4088 (
                    .b(inj_a_1755007766619_369),
                    .y(inj_y_1755007766661_650),
                    .a(temp_v_ts1755007766620)
                );
                mod_fixup_syntax_user mod_fixup_syntax_user_inst_1755007766658_6312 (
                    .fs_in(temp_v_ts1755007766620),
                    .fs_out(inj_fs_out_1755007766658_980)
                );
                // BEGIN: typedef_struct_public_mod_ts1755007766653
                typedef struct packed {
                    logic [7:0] field1_ts1755007766653;
                    logic [7:0] field2_ts1755007766653;
                } my_public_packed_struct_t;
                my_public_packed_struct_t my_struct_var;
                always_comb begin
                    my_struct_var = inj_in_u16_1755007766649_716;
                end
                assign inj_field2_o_1755007766653_601 = my_struct_var.field2_ts1755007766653;
                // END: typedef_struct_public_mod_ts1755007766653

                SignedUnsignedConversions SignedUnsignedConversions_inst_1755007766649_5070 (
                    .in_l32(inj_in_l32_1755007766649_548),
                    .in_s8(inj_in3_1755007766636_95),
                    .out_s32_from_int(inj_out_s32_from_int_1755007766649_11),
                    .in_u16(inj_in_u16_1755007766649_716),
                    .out_u8(inj_out_u8_1755007766649_918),
                    .out_s32_from_l32(inj_out_s32_from_l32_1755007766649_282),
                    .in_int(inj_in_int_1755007766649_449),
                    .out_u32_from_l32(inj_out_u32_from_l32_1755007766649_681),
                    .out_s16(inj_out_s16_1755007766649_176),
                    .out_u32_from_int(inj_out_u32_from_int_1755007766649_582)
                );
                split_single_stmt split_single_stmt_inst_1755007766646_6693 (
                    .out_q(inj_out_q_1755007766646_714),
                    .in_q(inj_data_case_b_1755007766618_205)
                );
                // BEGIN: param_local_port_ts1755007766644
                localparam int LP_BODY_VAL = 125;
                localparam int LP_CALCULATED = P_PORT_VAL + LP_BODY_VAL;
                always_comb begin
                    if (reset) begin
                        inj_o_sum_1755007766643_407 = 0;
                    end else begin
                        inj_o_sum_1755007766643_407 = LP_CALCULATED;
                    end
                end
                // END: param_local_port_ts1755007766644

                // BEGIN: bitwise_ops_ts1755007766641
                assign inj_out_1755007766641_654 = (inj_in3_1755007766636_95 & inj_data_case_b_1755007766618_205) | (~inj_data_case_a_1755007766618_718) ^ (inj_in3_1755007766636_95 << 2) >> 1;
                // END: bitwise_ops_ts1755007766641

                // BEGIN: variable_sel_mux_ts1755007766639
                assign inj_out_1755007766639_577 = inj_data_case_b_1755007766618_205[inj_index_1755007766621_160];
                // END: variable_sel_mux_ts1755007766639

                // BEGIN: remaining_reduction_ops_ts1755007766636
                assign inj_nand_out_1755007766636_680 = ~&inj_data_case_b_1755007766618_205;
                assign inj_nor_out_1755007766636_811 = ~|inj_data_case_a_1755007766618_718;
                assign inj_xnor_out_1755007766636_189 = ^~inj_in3_1755007766636_95;
                // END: remaining_reduction_ops_ts1755007766636

            assign temp_wire_ts1755007766634[7:4] = inj_in_h_1755007766634_835;
            assign temp_wire_ts1755007766634[3:0] = inj_in_l_1755007766634_157;
            assign inj_out_1755007766634_580 = temp_wire_ts1755007766634;
            // END: coalesced_assign_ts1755007766634

            // BEGIN: sequential_register_en_ts1755007766632
            always_ff @(posedge clk) begin
                if (temp_v_ts1755007766620) begin
                    inj_data_out_1755007766632_283 <= inj_data_case_a_1755007766618_718;
                end
            end
            // END: sequential_register_en_ts1755007766632

            func_macro_args func_macro_args_inst_1755007766630_6734 (
                .output_int(inj_output_int_1755007766630_252),
                .input_int(inj_b_1755007766619_530)
            );
            // BEGIN: PragmaProtectOptions_ts1755007766628
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
        assign inj_config_data_out_1755007766628_137 = inj_b_1755007766619_530 + 1;
            // END: PragmaProtectOptions_ts1755007766628

            SynchronousMemory SynchronousMemory_inst_1755007766626_8695 (
                .clk(clk),
                .read_address(inj_read_address_1755007766626_447),
                .rst(reset),
                .write_address(inj_write_address_1755007766626_863),
                .write_data(inj_data_case_b_1755007766618_205),
                .write_en(inj_a_1755007766619_369),
                .read_data(inj_read_data_1755007766626_243)
            );
            // BEGIN: virtual_interface_lookup_mod_ts1755007766623
            always_comb begin
                inj_out_data_1755007766623_699  = inj_data_case_b_1755007766618_205;
                inj_out_valid_1755007766623_2 = inj_a_1755007766619_369;
                inj_dummy_out_1755007766623_705 = temp_v_ts1755007766620;
            end
            // END: virtual_interface_lookup_mod_ts1755007766623

            // BEGIN: module_selection_ts1755007766622
            always_comb begin
            inj_out_vector_assign_1755007766622_176 = inj_in_vector_1755007766622_582;
            inj_out_bit_select_1755007766622_668 = inj_in_vector_1755007766622_582[inj_in_index_1755007766622_729];
            inj_out_part_select_1755007766622_380 = inj_in_vector_1755007766622_582[inj_in_part_lsb_1755007766622_900 +: 4];
            inj_out_bitwise_ops_1755007766622_464 = inj_in_vector_1755007766622_582 & {8{clk}};
            end
            // END: module_selection_ts1755007766622

            variable_sel_mux variable_sel_mux_inst_1755007766621_1467 (
                .index(inj_index_1755007766621_160),
                .out(inj_out_1755007766621_853),
                .in(inj_data_case_a_1755007766618_718)
            );
        temp_v_ts1755007766620 = d_ts1755007766620;
        c_ts1755007766620      = temp_v_ts1755007766620;
    end
    assign inj_out_a_1755007766619_132 = inj_a_1755007766619_369;
    assign d_ts1755007766620     = inj_b_1755007766619_530;
    assign inj_out_b_1755007766619_737 = d_ts1755007766620 + P1 + LP1;
    // END: ModuleBasic_ts1755007766620

    mod_split_case mod_split_case_inst_1755007766619_2590 (
        .out_case_b(inj_out_case_b_1755007766619_127),
        .data_in(inj_data_case_a_1755007766618_718),
        .sel(inj_select_case_1755007766618_511),
        .out_case_a(inj_out_case_a_1755007766619_719)
    );
    my_if case_vif_inst();
    always_comb begin
        case (inj_select_case_1755007766618_511)
            2'b00: begin
                case_vif_inst.data = 8'hAA;
                case_vif_inst.valid = 1'b1;
                case_vif_inst.ready = 1'b0;
            end
            2'b01: begin
                case_vif_inst.data = inj_data_case_a_1755007766618_718;
                case_vif_inst.valid = 1'b0;
                case_vif_inst.ready = 1'b1;
            end
            2'b10: begin
                case_vif_inst.data = inj_data_case_b_1755007766618_205;
                case_vif_inst.valid = 1'b1;
                case_vif_inst.ready = 1'b1;
            end
            default: begin
                case_vif_inst.data = 8'hFF;
                case_vif_inst.valid = 1'b0;
                case_vif_inst.ready = 1'b0;
            end
        endcase
        inj_case_output_ready_1755007766618_199 = case_vif_inst.ready;
    end
    // END: module_case_write_ts1755007766618

    assign inj_data_d_1755007766617_205 = clk;
    // END: simple_logic_b_ts1755007766618
endmodule

