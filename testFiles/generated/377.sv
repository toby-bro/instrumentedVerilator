interface MyInterface (
    input logic clk
);
    logic req;
    logic valid;
    modport master (output req, input valid, input clk);
    modport slave (input req, output valid, input clk);
endinterface
interface simple_if (
    input logic clk
);
    logic data;
    logic ready;
    modport master (output data, input ready);
    modport slave (input data, output ready);
endinterface
module case_default (
    input logic [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b01: out_res = 1'b1;
            2'b10: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule

module member_access_packed_union (
    input logic [31:0] in_val,
    input bit select_a,
    output logic [31:0] out_val
);
    typedef union packed {
        logic [31:0] a; 
        logic [31:0] b; 
    } my_packed_union;
    my_packed_union union_var;
    always_comb begin
        if (select_a)
            union_var.a = in_val;
        else
            union_var.b = in_val[31:0];
        out_val = union_var.a;
    end
endmodule

module mod_fixup_target (
    input logic fs_in_target,
    output logic fs_out_target
);
    assign fs_out_target = fs_in_target;
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

module mod_split_if (
    input logic clk,
    input logic cond,
    input logic [7:0] data_in,
    input logic reset,
    output logic [7:0] out_if_a,
    output logic [7:0] out_if_b
);
    logic [7:0]  split_if_var;
    logic [7:0] other_if_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_if_var <= 8'b0;
            other_if_var <= 8'b0;
        end else begin
            if (cond) begin
                split_if_var <= data_in;
                other_if_var <= data_in + 3;
            end else begin
                split_if_var <= data_in - 1;
                other_if_var <= data_in - 2;
            end
        end
    end
    always_comb begin
        out_if_a = split_if_var;
        out_if_b = other_if_var;
    end
endmodule

module more_procedural (
    input logic [31:0] p_in1,
    input logic [31:0] p_in2,
    input logic [1:0] p_mode,
    output logic [31:0] p_out
);
    always_comb begin
        case (p_mode)
            2'b00: p_out = (p_in1 + p_in2) * 2;
            2'b01: p_out = (p_in1 - p_in2) / 3; 
            2'b10: p_out = (p_in1 << 4) | (p_in2 >> 2);
            default: p_out = ~(p_in1 ^ p_in2) + 1;
        endcase
    end
endmodule

module nested_blocks (
    input logic data_value,
    input logic level1_en,
    input logic level2_en,
    output logic result_out
);
    always_comb begin : main_block 
        result_out = 1'b0; 
        if (level1_en) begin : inner_block1 
            if (level2_en) begin : inner_block2 
                result_out = data_value;
            end 
        end 
    end
endmodule

module not_a_hierarchical_scope_diag_mod (
    input logic [7:0] in_var,
    output logic [7:0] out_var
);
    logic [7:0] simple_var_nahsdm;
    always_comb simple_var_nahsdm = in_var;
    assign out_var = simple_var_nahsdm;
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

module split_complex_blocking (
    input logic [7:0] i1_r,
    input logic [7:0] i2_r,
    input logic [7:0] i3_r,
    output logic [7:0] o1_r,
    output logic [7:0] o2_r,
    output logic [7:0] o3_r
);
    logic [7:0] t1_r, t2_r;
    always @(*) begin
        t1_r = i1_r + i2_r;
        o1_r = t1_r - i3_r;
        t2_r = i2_r * i3_r;
        o2_r = t1_r + t2_r;
        o3_r = t2_r / 2;
    end
endmodule

module sub_module (
    input logic sub_in,
    output logic sub_out
);
    assign sub_out = !sub_in;
endmodule

module snippet (
    input wire clk,
    input logic inj_data_value_1755007880686_329,
    input logic [7:0] inj_i3_r_1755007880699_504,
    input int inj_in_val_1755007880686_52,
    input logic [31:0] inj_in_val_1755007880686_638,
    input logic [7:0] inj_in_wide_1755007880686_905,
    input logic [4:0] inj_index_1755007880709_550,
    input logic inj_level1_en_1755007880686_960,
    input logic inj_level2_en_1755007880686_18,
    input logic [2:0] inj_mode_1755007880688_263,
    input logic [31:0] inj_p_in2_1755007880714_589,
    input logic [1:0] inj_sel_1755007880687_369,
    input bit inj_select_a_1755007880686_70,
    input logic [7:0] inj_val1_1755007880688_544,
    input wire reset,
    output logic [7:0] inj_final_result_1755007880709_41,
    output logic inj_fs_out_target_1755007880706_86,
    output logic inj_main_out_1755007880707_526,
    output logic [7:0] inj_o1_r_1755007880699_472,
    output logic [7:0] inj_o2_r_1755007880699_532,
    output logic [7:0] inj_o3_r_1755007880699_963,
    output logic [7:0] inj_o_sum_1755007880692_770,
    output logic [7:0] inj_out1_a_1755007880693_870,
    output logic [7:0] inj_out_case_a_1755007880687_68,
    output logic [7:0] inj_out_case_b_1755007880687_851,
    output logic [7:0] inj_out_if_a_1755007880688_832,
    output logic [7:0] inj_out_if_b_1755007880688_873,
    output logic [3:0] inj_out_narrow_1755007880686_476,
    output reg inj_out_res_1755007880690_717,
    output reg inj_out_res_1755007880704_395,
    output reg inj_out_res_1755007880718_102,
    output logic [31:0] inj_out_val_1755007880686_325,
    output int inj_out_val_1755007880686_579,
    output int inj_out_val_1755007880702_952,
    output logic [7:0] inj_out_val_c_1755007880703_33,
    output logic [7:0] inj_out_var_1755007880695_835,
    output logic [31:0] inj_p_out_1755007880714_686,
    output logic inj_q_out_1755007880697_248,
    output logic [7:0] inj_res_1755007880688_908,
    output logic inj_result_out_1755007880686_912,
    output logic inj_udnt_output_1755007880700_416,
    output logic inj_uout_1755007880700_844,
    output logic inj_valid_out_1755007880687_116
);
    // BEGIN: module_in_program_ref_ts1755007880686
    // BEGIN: LintImplicitWidth_ts1755007880686
    // BEGIN: ModuleWithInterface_ts1755007880687
    // BEGIN: dup_nested_if_ts1755007880689
    // BEGIN: case_default_ts1755007880690
    // BEGIN: split_basic_blocking_ts1755007880693
    // BEGIN: LogicDependencyChain_ts1755007880698
    logic q1_ts1755007880697, q2_ts1755007880697;
        // BEGIN: split_seq_dependency_ts1755007880703
        logic [7:0] mid_val_c_ts1755007880703;
            // BEGIN: dup_literal_param_ts1755007880710
            parameter CONST_A = 8'd10;
            localparam CONST_B = 8'd20;
            parameter CONST_C = 10;
            localparam CONST_D = 8'hFF;
            parameter CONST_E = 8'b01010101;
            logic [7:0] temp1_ts1755007880710, temp2_ts1755007880710;
            assign temp1_ts1755007880710 = inj_index_1755007880709_550 + CONST_A;
            assign temp2_ts1755007880710 = inj_index_1755007880709_550 + 10;
            always_comb begin
                logic [7:0] local_temp_ts1755007880710;
                    case_default case_default_inst_1755007880718_5502 (
                        .in_val(inj_sel_1755007880687_369),
                        .out_res(inj_out_res_1755007880718_102)
                    );
                    more_procedural more_procedural_inst_1755007880714_7515 (
                        .p_mode(inj_sel_1755007880687_369),
                        .p_out(inj_p_out_1755007880714_686),
                        .p_in1(inj_in_val_1755007880686_638),
                        .p_in2(inj_p_in2_1755007880714_589)
                    );
                local_temp_ts1755007880710 = inj_index_1755007880709_550 * CONST_B;
                inj_final_result_1755007880709_41 = temp1_ts1755007880710 + temp2_ts1755007880710 + local_temp_ts1755007880710;
                if (inj_index_1755007880709_550 > 5) begin
                    inj_final_result_1755007880709_41 = inj_final_result_1755007880709_41 + 1;
                end else if (inj_index_1755007880709_550 < CONST_C) begin
                    inj_final_result_1755007880709_41 = inj_final_result_1755007880709_41 - 1;
                end
                case (inj_index_1755007880709_550)
                    5'd0: inj_final_result_1755007880709_41 = CONST_A;
                    5'd1: inj_final_result_1755007880709_41 = 20;
                    5'd2: inj_final_result_1755007880709_41 = 10;
                    5'd3: inj_final_result_1755007880709_41 = CONST_B;
                    5'd4: inj_final_result_1755007880709_41 = CONST_D;
                    5'd5: inj_final_result_1755007880709_41 = 8'hFF;
                    default: inj_final_result_1755007880709_41 = CONST_E;
                endcase
            end
            // END: dup_literal_param_ts1755007880710

            // BEGIN: hierarchy_if_ts1755007880708
            sub_module u_sub (
                .sub_in(q1_ts1755007880697),
                .sub_out(inj_main_out_1755007880707_526)
            );
            simple_if if_inst (.clk(clk));
            always_comb begin
                if_inst.data = q1_ts1755007880697;
                if_inst.ready = inj_main_out_1755007880707_526;
            end
            // END: hierarchy_if_ts1755007880708

            mod_fixup_target mod_fixup_target_inst_1755007880706_1211 (
                .fs_out_target(inj_fs_out_target_1755007880706_86),
                .fs_in_target(inj_data_value_1755007880686_329)
            );
            // BEGIN: case_basic_ts1755007880704
            always_comb begin
                inj_out_res_1755007880704_395 = 1'b0;
                case (inj_sel_1755007880687_369)
                    2'b00: inj_out_res_1755007880704_395 = 1'b0;
                    2'b01: inj_out_res_1755007880704_395 = 1'b1;
                    2'b10: inj_out_res_1755007880704_395 = 1'b0;
                    2'b11: inj_out_res_1755007880704_395 = 1'b1;
                endcase
            end
            // END: case_basic_ts1755007880704

        always @(posedge clk) begin
            mid_val_c_ts1755007880703 <= inj_i3_r_1755007880699_504 + 1;
            inj_out_val_c_1755007880703_33 <= mid_val_c_ts1755007880703 * 2;
        end
        // END: split_seq_dependency_ts1755007880703

        // BEGIN: recursive_param_diag_mod_ts1755007880702
        assign inj_out_val_1755007880702_952 = inj_in_val_1755007880686_52;
        // END: recursive_param_diag_mod_ts1755007880702

        // BEGIN: udnt_port_module_ts1755007880700
        assign inj_uout_1755007880700_844 = q1_ts1755007880697;
        assign inj_udnt_output_1755007880700_416 = inj_level1_en_1755007880686_960;
        // END: udnt_port_module_ts1755007880700

        split_complex_blocking split_complex_blocking_inst_1755007880699_5989 (
            .o1_r(inj_o1_r_1755007880699_472),
            .o2_r(inj_o2_r_1755007880699_532),
            .o3_r(inj_o3_r_1755007880699_963),
            .i1_r(inj_val1_1755007880688_544),
            .i2_r(inj_in_wide_1755007880686_905),
            .i3_r(inj_i3_r_1755007880699_504)
        );
    always @(posedge clk) begin
        q1_ts1755007880697 <= inj_data_value_1755007880686_329;
    end
    always @(q1_ts1755007880697) begin
        q2_ts1755007880697 = ~q1_ts1755007880697;
    end
    assign inj_q_out_1755007880697_248 = q2_ts1755007880697;
    // END: LogicDependencyChain_ts1755007880698

    not_a_hierarchical_scope_diag_mod not_a_hierarchical_scope_diag_mod_inst_1755007880695_3986 (
        .out_var(inj_out_var_1755007880695_835),
        .in_var(inj_val1_1755007880688_544)
    );
    always @(*) begin
        inj_out1_a_1755007880693_870 = inj_val1_1755007880688_544;
    end
    // END: split_basic_blocking_ts1755007880693

    param_local_port param_local_port_inst_1755007880692_3643 (
        .i_reset(reset),
        .o_sum(inj_o_sum_1755007880692_770)
    );
    always_comb begin
        inj_out_res_1755007880690_717 = 1'b0;
        case (inj_sel_1755007880687_369)
            2'b01: inj_out_res_1755007880690_717 = 1'b1;
            2'b10: inj_out_res_1755007880690_717 = 1'b0;
            default: inj_out_res_1755007880690_717 = 1'b1;
        endcase
    end
    // END: case_default_ts1755007880690

    always_comb begin
        inj_res_1755007880688_908 = '0;
        if (inj_mode_1755007880688_263 == 3'b001) begin
            if (inj_val1_1755007880688_544 > inj_in_wide_1755007880686_905) begin
                inj_res_1755007880688_908 = inj_val1_1755007880688_544 + inj_in_wide_1755007880686_905;
            end else begin
                inj_res_1755007880688_908 = inj_val1_1755007880688_544 - inj_in_wide_1755007880686_905;
            end
        end else if (inj_mode_1755007880688_263 == 3'b010) begin
            if (inj_val1_1755007880688_544 > inj_in_wide_1755007880686_905) begin
                inj_res_1755007880688_908 = inj_val1_1755007880688_544 + inj_in_wide_1755007880686_905;
            end else begin
                inj_res_1755007880688_908 = inj_val1_1755007880688_544 - inj_in_wide_1755007880686_905;
            end
        end else if (inj_mode_1755007880688_263 == 3'b011) begin
            if (inj_val1_1755007880688_544 < inj_in_wide_1755007880686_905) begin
                inj_res_1755007880688_908 = inj_val1_1755007880688_544 * inj_in_wide_1755007880686_905;
            end else begin
                inj_res_1755007880688_908 = inj_val1_1755007880688_544 / ((inj_in_wide_1755007880686_905 == 0) ? 1 : inj_in_wide_1755007880686_905);
            end
        end else if (inj_mode_1755007880688_263 == 3'b100) begin
            if (inj_val1_1755007880688_544 != inj_in_wide_1755007880686_905) begin
                if (inj_val1_1755007880688_544 > inj_in_wide_1755007880686_905) inj_res_1755007880688_908 = inj_val1_1755007880688_544;
                else inj_res_1755007880688_908 = inj_in_wide_1755007880686_905;
            end else begin
                inj_res_1755007880688_908 = inj_val1_1755007880688_544 + inj_in_wide_1755007880686_905;
            end
        end
        else begin
            inj_res_1755007880688_908 = inj_val1_1755007880688_544 ^ inj_in_wide_1755007880686_905;
        end
    end
    // END: dup_nested_if_ts1755007880689

    mod_split_if mod_split_if_inst_1755007880688_339 (
        .data_in(inj_in_wide_1755007880686_905),
        .reset(reset),
        .out_if_a(inj_out_if_a_1755007880688_832),
        .out_if_b(inj_out_if_b_1755007880688_873),
        .clk(clk),
        .cond(inj_data_value_1755007880686_329)
    );
    MyInterface my_if (clk);
    assign my_if.req = 1'b1;
    assign inj_valid_out_1755007880687_116 = my_if.valid;
    // END: ModuleWithInterface_ts1755007880687

    mod_split_case mod_split_case_inst_1755007880687_2500 (
        .out_case_a(inj_out_case_a_1755007880687_68),
        .out_case_b(inj_out_case_b_1755007880687_851),
        .data_in(inj_in_wide_1755007880686_905),
        .sel(inj_sel_1755007880687_369)
    );
    nested_blocks nested_blocks_inst_1755007880686_3927 (
        .data_value(inj_data_value_1755007880686_329),
        .level1_en(inj_level1_en_1755007880686_960),
        .level2_en(inj_level2_en_1755007880686_18),
        .result_out(inj_result_out_1755007880686_912)
    );
    assign inj_out_narrow_1755007880686_476 = inj_in_wide_1755007880686_905;
    // END: LintImplicitWidth_ts1755007880686

    member_access_packed_union member_access_packed_union_inst_1755007880686_5823 (
        .out_val(inj_out_val_1755007880686_325),
        .in_val(inj_in_val_1755007880686_638),
        .select_a(inj_select_a_1755007880686_70)
    );
    assign inj_out_val_1755007880686_579 = inj_in_val_1755007880686_52;
    // END: module_in_program_ref_ts1755007880686
endmodule

