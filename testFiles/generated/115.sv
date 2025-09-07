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

module casez_xz_alt (
    input logic [2:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        casez (in_val)
            3'b1?z: out_res = 1'b1;
            3'b0z?: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule

module mod_comb_logic (
    input logic a,
    input logic b,
    output logic y
);
    always_comb begin
        y = a & b;
    end
endmodule

module mod_fixup_target (
    input logic fs_in_target,
    output logic fs_out_target
);
    assign fs_out_target = fs_in_target;
endmodule

module mod_sub (
    input wire in_sub,
    output logic out_sub
);
    assign out_sub = in_sub;
endmodule

module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
endmodule

module split_seq_dependency (
    input logic clk_c,
    input logic [7:0] in_val_c,
    output logic [7:0] out_val_c
);
    logic [7:0] mid_val_c;
    always @(posedge clk_c) begin
        mid_val_c <= in_val_c + 1;
        out_val_c <= mid_val_c * 2;
    end
endmodule

module system_names_mod (
    input int in_val,
    output int out_val
);
    assign out_val = $bits(in_val);
endmodule

module target_module_for_bind (
    input logic i_target_clk,
    input logic [7:0] i_target_data,
    output logic [7:0] o_target_result
);
    always_comb o_target_result = i_target_data + 1;
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_data_in_1755007791235_536,
    input logic [7:0] inj_in1_1755007791218_910,
    input logic [31:0] inj_in1_1755007791219_895,
    input logic [7:0] inj_in2_1755007791218_869,
    input logic [31:0] inj_in2_1755007791219_176,
    input bit [7:0] inj_in_cmd_1755007791221_25,
    input wire [1:0] inj_in_const_index_1755007791220_16,
    input wire [7:0] inj_in_data_1755007791220_719,
    input wire [1:0] inj_in_index_1755007791220_472,
    input wire [2:0] inj_in_index_1755007791237_970,
    input bit [3:0] inj_in_mask_x_1755007791226_969,
    input int inj_in_val_1755007791218_385,
    input logic [2:0] inj_in_val_1755007791220_496,
    input logic [15:0] inj_packed_in_1755007791224_337,
    input logic inj_udnt_input_1755007791218_228,
    input logic inj_uin_1755007791218_203,
    input wire reset,
    output logic [7:0] inj_data_out_1755007791235_396,
    output logic [7:0] inj_field2_o_1755007791224_960,
    output logic inj_fs_out_target_1755007791218_727,
    output logic [7:0] inj_o_result_1755007791246_935,
    output logic inj_o_status_1755007791246_678,
    output logic inj_out1_1755007791243_123,
    output logic inj_out_1755007791218_768,
    output logic [31:0] inj_out_1755007791219_165,
    output logic [7:0] inj_out_array_sel_const_1755007791220_293,
    output logic [7:0] inj_out_array_sel_var_1755007791220_104,
    output logic inj_out_bit_select_1755007791237_127,
    output logic [1:0] inj_out_bits_1755007791218_236,
    output logic [7:0] inj_out_bitwise_ops_1755007791237_699,
    output bit [1:0] inj_out_match_type_x_1755007791226_104,
    output logic [3:0] inj_out_part_select_1755007791237_977,
    output reg inj_out_res_1755007791220_742,
    output logic [7:0] inj_out_slice_1755007791240_419,
    output bit [3:0] inj_out_status_1755007791221_342,
    output logic inj_out_sub_1755007791232_348,
    output int inj_out_val_1755007791218_782,
    output logic [7:0] inj_out_val_c_1755007791229_229,
    output logic [7:0] inj_out_vector_assign_1755007791237_262,
    output logic inj_udnt_output_1755007791218_160,
    output logic inj_uout_1755007791218_108,
    output logic inj_y_1755007791223_87
);
    // BEGIN: reduction_ops_ts1755007791218
    // BEGIN: udnt_port_module_ts1755007791218
    // BEGIN: cast_select_demo_ts1755007791219
    logic [7:0] internal_ts1755007791219;
        // BEGIN: Mod_ArrayOps_ts1755007791221
        logic [7:0] my_array_ts1755007791221 [3:0];
            // BEGIN: ModuleLineDirective_ts1755007791243
            logic internal_sig_a_ts1755007791243;
            logic internal_sig_b_ts1755007791243;
            logic unused_line_var_ts1755007791243;
                // BEGIN: bind_directive_top_ts1755007791247
                target_module_for_bind target_inst(
                    .i_target_clk   (clk),
                    .i_target_data  (my_array_ts1755007791221),
                    .o_target_result(inj_o_result_1755007791246_935)
                );
                module_to_bind bind_inst(
                    .i_bind_clk     (clk),
                    .i_bind_control (inj_data_in_1755007791235_536),
                    .o_bind_status  (inj_o_status_1755007791246_678)
                );
                // END: bind_directive_top_ts1755007791247

            `line 100 "virtual_file_A.sv" 1
            assign internal_sig_a_ts1755007791243 = inj_udnt_input_1755007791218_228;
            `line 20 "virtual_file_B.sv" 1
            assign internal_sig_b_ts1755007791243 = ~internal_sig_a_ts1755007791243;
            assign unused_line_var_ts1755007791243 = 1'b1;
            `line 150 "virtual_file_A.sv" 2
            assign inj_out1_1755007791243_123 = internal_sig_b_ts1755007791243;
            `line 1 "original_file.sv" 0
            // END: ModuleLineDirective_ts1755007791243

            // BEGIN: MiscExpressions_ValueRange_ts1755007791240
            always_comb begin
                inj_out_slice_1755007791240_419 = inj_packed_in_1755007791224_337[7:0];
            end
            // END: MiscExpressions_ValueRange_ts1755007791240

            // BEGIN: module_selection_ts1755007791238
            always_comb begin
            inj_out_vector_assign_1755007791237_262 = inj_in_data_1755007791220_719;
            inj_out_bit_select_1755007791237_127 = inj_in_data_1755007791220_719[inj_in_index_1755007791237_970];
            inj_out_part_select_1755007791237_977 = inj_in_data_1755007791220_719[inj_in_const_index_1755007791220_16 +: 4];
            inj_out_bitwise_ops_1755007791237_699 = inj_in_data_1755007791220_719 & {8{clk}};
            end
            // END: module_selection_ts1755007791238

            ModuleHierarchy_Low ModuleHierarchy_Low_inst_1755007791235_7113 (
                .data_out(inj_data_out_1755007791235_396),
                .data_in(inj_data_in_1755007791235_536),
                .sel_in(inj_in_val_1755007791218_385)
            );
            mod_sub mod_sub_inst_1755007791232_8511 (
                .in_sub(clk),
                .out_sub(inj_out_sub_1755007791232_348)
            );
            split_seq_dependency split_seq_dependency_inst_1755007791229_1095 (
                .clk_c(clk),
                .in_val_c(inj_in2_1755007791218_869),
                .out_val_c(inj_out_val_c_1755007791229_229)
            );
            // BEGIN: mod_casex_wildcard_overlap_priority_ts1755007791227
        always_comb begin
            inj_out_match_type_x_1755007791226_104 = 2'b01;
            priority casex (inj_in_mask_x_1755007791226_969)
                4'b1X0Z: begin
                    inj_out_match_type_x_1755007791226_104 = 2'b10;
                end
                4'b10?Z: begin
                    inj_out_match_type_x_1755007791226_104 = 2'b11;
                end
                4'bZ1?X: begin
                    inj_out_match_type_x_1755007791226_104 = 2'b00;
                end
                default: begin
                    inj_out_match_type_x_1755007791226_104 = 2'b01;
                end
            endcase
        end
            // END: mod_casex_wildcard_overlap_priority_ts1755007791227

            // BEGIN: typedef_struct_public_mod_ts1755007791225
            typedef struct packed {
                logic [7:0] field1_ts1755007791225;
                logic [7:0] field2_ts1755007791225;
            } my_public_packed_struct_t;
            my_public_packed_struct_t my_struct_var;
            always_comb begin
                my_struct_var = inj_packed_in_1755007791224_337;
            end
            assign inj_field2_o_1755007791224_960 = my_struct_var.field2_ts1755007791225;
            // END: typedef_struct_public_mod_ts1755007791225

            mod_comb_logic mod_comb_logic_inst_1755007791223_9669 (
                .y(inj_y_1755007791223_87),
                .a(inj_uin_1755007791218_203),
                .b(inj_udnt_input_1755007791218_228)
            );
            // BEGIN: mod_case_standard_ts1755007791222
        always_comb begin
            case (inj_in_cmd_1755007791221_25)
                8'd0, 8'd1, 8'd2: begin
                    inj_out_status_1755007791221_342 = 4'hA;
                end
                8'd3, 8'd4: begin
                    inj_out_status_1755007791221_342 = 4'hB;
                end
                default: begin
                    inj_out_status_1755007791221_342 = 4'hF;
                end
            endcase
        end
            // END: mod_case_standard_ts1755007791222

        always_comb begin
            my_array_ts1755007791221[0] = inj_in_data_1755007791220_719;
            my_array_ts1755007791221[1] = inj_in_data_1755007791220_719 + 8'd1;
            my_array_ts1755007791221[2] = inj_in_data_1755007791220_719 + 8'd2;
            my_array_ts1755007791221[3] = inj_in_data_1755007791220_719 + 8'd3;
            inj_out_array_sel_var_1755007791220_104 = my_array_ts1755007791221[inj_in_index_1755007791220_472];
            inj_out_array_sel_const_1755007791220_293 = my_array_ts1755007791221[inj_in_const_index_1755007791220_16];
        end
        // END: Mod_ArrayOps_ts1755007791221

        casez_xz_alt casez_xz_alt_inst_1755007791220_269 (
            .in_val(inj_in_val_1755007791220_496),
            .out_res(inj_out_res_1755007791220_742)
        );
        // BEGIN: always_comb_if_ts1755007791219
        always_comb begin
            if (inj_udnt_input_1755007791218_228) begin
                inj_out_1755007791219_165 = inj_in1_1755007791219_895;
            end else begin
                inj_out_1755007791219_165 = inj_in2_1755007791219_176;
            end
        end
        // END: always_comb_if_ts1755007791219

    always_comb begin
        internal_ts1755007791219 = inj_in1_1755007791218_910;
        inj_out_bits_1755007791218_236 = internal_ts1755007791219[3 -: 2];
    end
    // END: cast_select_demo_ts1755007791219

    mod_fixup_target mod_fixup_target_inst_1755007791218_7358 (
        .fs_in_target(inj_udnt_input_1755007791218_228),
        .fs_out_target(inj_fs_out_target_1755007791218_727)
    );
    system_names_mod system_names_mod_inst_1755007791218_9791 (
        .out_val(inj_out_val_1755007791218_782),
        .in_val(inj_in_val_1755007791218_385)
    );
    assign inj_uout_1755007791218_108 = inj_uin_1755007791218_203;
    assign inj_udnt_output_1755007791218_160 = inj_udnt_input_1755007791218_228;
    // END: udnt_port_module_ts1755007791218

    assign inj_out_1755007791218_768 = &inj_in1_1755007791218_910 | ^inj_in2_1755007791218_869;
    // END: reduction_ops_ts1755007791218
endmodule

