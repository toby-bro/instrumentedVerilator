interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module AlwaysCombInvert (
    input logic [3:0] a,
    output logic [3:0] y
);
    always_comb y = ~a;
endmodule

module always_comb_if (
    input logic cond,
    input logic [31:0] in1,
    input logic [31:0] in2,
    output logic [31:0] out
);
    always_comb begin
        if (cond) begin
            out = in1;
        end else begin
            out = in2;
        end
    end
endmodule

module attributes_test (
    input logic i_attr_in,
    output logic o_attr_out
);
    (* synthesis_preserve *) logic internal_signal;
    always_comb begin : my_combinational_block
        internal_signal = i_attr_in ? 1'b1 : 1'b0;
        o_attr_out      = internal_signal;
    end
endmodule

module casez_xz (
    input logic [2:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        casez (in_val)
            3'b1??: out_res = 1'b1;
            3'b0z?: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule

module module_selection (
    input wire in_bit,
    input wire [2:0] in_index,
    input wire [1:0] in_part_lsb,
    input wire [7:0] in_vector,
    output logic out_bit_select,
    output logic [7:0] out_bitwise_ops,
    output logic [3:0] out_part_select,
    output logic [7:0] out_vector_assign
);
    always_comb begin
    out_vector_assign = in_vector;
    out_bit_select = in_vector[in_index];
    out_part_select = in_vector[in_part_lsb +: 4];
    out_bitwise_ops = in_vector & {8{in_bit}};
    end
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

module range_select_indexed_packed (
    input logic [31:0] in_vec,
    input int start_index,
    input int width,
    output logic [7:0] out_down,
    output logic [7:0] out_up
);
    always_comb begin
        if (start_index >= 0 && width > 0 && start_index + width <= 32) begin
            case (width)
                1: out_up = in_vec[start_index +: 1];
                2: out_up = in_vec[start_index +: 2];
                4: out_up = in_vec[start_index +: 4];
                8: out_up = in_vec[start_index +: 8];
                default: out_up = 'x;
            endcase
        end else begin
            out_up = 'x;
        end
        if (start_index >= width - 1 && width > 0 && start_index < 32) begin
            case (width)
                1: out_down = in_vec[start_index -: 1];
                2: out_down = in_vec[start_index -: 2];
                4: out_down = in_vec[start_index -: 4];
                8: out_down = in_vec[start_index -: 8];
                default: out_down = 'x;
            endcase
        end else begin
            out_down = 'x;
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

module split_multiple_blocking (
    input logic [3:0] data_in_n,
    output logic [3:0] data_out1_n,
    output logic [3:0] data_out2_n
);
    logic [3:0] temp_n;
    always @(*) begin
        temp_n = data_in_n + 1;
        data_out1_n = temp_n * 2;
        data_out2_n = temp_n + 3;
    end
endmodule

module sub_inst_array_mod (
    input logic [7:0] in,
    output logic [7:0] out
);
    assign out = in;
endmodule

module target_module_for_bind (
    input logic i_target_clk,
    input logic [7:0] i_target_data,
    output logic [7:0] o_target_result
);
    always_comb o_target_result = i_target_data + 1;
endmodule

module unknown_class_pkg_diag_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_a_1755007855195_44,
    input logic inj_cond_1755007855191_557,
    input logic [7:0] inj_i3_r_1755007855194_135,
    input logic [31:0] inj_in1_1755007855191_835,
    input logic [31:0] inj_in2_1755007855191_583,
    input bit [7:0] inj_in_cmd_1755007855242_894,
    input wire [2:0] inj_in_index_1755007855191_50,
    input wire [1:0] inj_in_part_lsb_1755007855191_337,
    input int inj_in_val_1755007855192_813,
    input logic [2:0] inj_in_val_1755007855196_259,
    input logic [15:0] inj_in_vec_1755007855213_769,
    input wire [7:0] inj_in_vector_1755007855191_276,
    input logic [7:0] inj_op1_u_1755007855191_882,
    input logic [7:0] inj_op2_u_1755007855191_345,
    input int inj_start_index_1755007855195_319,
    input wire reset,
    output logic inj_concat_port_output_1755007855234_948,
    output logic inj_concat_port_output_1755007855255_472,
    output logic [7:0] inj_data_1755007855225_229,
    output logic [7:0] inj_data_a_out_task_1755007855201_742,
    output logic [7:0] inj_data_b_out_task_1755007855201_729,
    output logic [3:0] inj_data_out1_n_1755007855223_796,
    output logic [3:0] inj_data_out2_n_1755007855223_898,
    output logic [7:0] inj_data_out_1755007855217_528,
    output logic [7:0] inj_diff_u_1755007855191_648,
    output wire inj_dout_1755007855211_364,
    output logic [1:0] inj_non_ansi_i_1755007855234_221,
    output logic [1:0] inj_non_ansi_i_1755007855255_161,
    output logic [1:0] inj_non_ansi_j_1755007855234_290,
    output logic [1:0] inj_non_ansi_j_1755007855255_656,
    output logic [7:0] inj_o1_r_1755007855194_957,
    output logic [7:0] inj_o2_r_1755007855194_103,
    output logic [7:0] inj_o3_r_1755007855194_808,
    output logic inj_o_attr_out_1755007855231_347,
    output logic inj_o_p_and_1755007855249_328,
    output logic inj_o_p_xor_1755007855249_129,
    output logic [7:0] inj_o_target_result_1755007855200_227,
    output logic [7:0] inj_out1_f_1755007855197_304,
    output logic [7:0] inj_out2_f_1755007855197_944,
    output logic [7:0] inj_out3_f_1755007855197_889,
    output logic [31:0] inj_out_1755007855191_11,
    output logic [7:0] inj_out_1755007855220_404,
    output wire inj_out_1755007855228_420,
    output logic [7:0] inj_out_1755007855237_443,
    output logic inj_out_bit_select_1755007855191_748,
    output logic [7:0] inj_out_bitwise_ops_1755007855191_649,
    output logic inj_out_data_q_1755007855204_729,
    output logic [7:0] inj_out_down_1755007855195_853,
    output logic inj_out_i_1755007855208_500,
    output logic [3:0] inj_out_part_select_1755007855191_193,
    output reg inj_out_res_1755007855196_852,
    output logic [7:0] inj_out_slice_be_1755007855213_256,
    output logic [7:0] inj_out_slice_le_1755007855213_263,
    output bit [3:0] inj_out_status_1755007855242_318,
    output logic [7:0] inj_out_up_1755007855195_391,
    output int inj_out_val_1755007855192_937,
    output logic [7:0] inj_out_val_1755007855206_926,
    output logic [7:0] inj_out_vec_y_1755007855193_114,
    output logic [7:0] inj_out_vector_assign_1755007855191_807,
    output logic [7:0] inj_prod_u_1755007855191_724,
    output logic [7:0] inj_sum_u_1755007855191_290,
    output logic [3:0] inj_y_1755007855195_216,
    output logic [3:0] inj_y_1755007855199_646
);
    // BEGIN: split_arith_blocking_ts1755007855191
    // BEGIN: split_vector_assign_ts1755007855193
    // BEGIN: split_independent_nb_ts1755007855198
    // BEGIN: module_task_args_ts1755007855202
    logic [7:0] data_a_ts1755007855202 ;
    logic [7:0] data_b_ts1755007855202 ;
        // BEGIN: ContinuousWire_ts1755007855211
        wire internal_w_ts1755007855211;
            // BEGIN: non_ansi_concat_port_ts1755007855234
            output logic [1:0] inj_non_ansi_i_1755007855234_221_ts1755007855234;
            output logic [1:0] inj_non_ansi_j_1755007855234_290_ts1755007855234;
            input logic inj_cond_1755007855191_557_ts1755007855234;
            output logic inj_concat_port_output_1755007855234_948_ts1755007855234;
                // BEGIN: non_ansi_concat_port_ts1755007855256
                output logic [1:0] inj_non_ansi_i_1755007855255_161_ts1755007855255;
                output logic [1:0] inj_non_ansi_j_1755007855255_656_ts1755007855255;
                input logic inj_cond_1755007855191_557_ts1755007855234_ts1755007855255;
                output logic inj_concat_port_output_1755007855255_472_ts1755007855255;
                assign inj_non_ansi_i_1755007855255_161_ts1755007855255 = 2'b10;
                assign inj_non_ansi_j_1755007855255_656_ts1755007855255 = 2'b01;
                assign inj_concat_port_output_1755007855255_472_ts1755007855255 = inj_cond_1755007855191_557_ts1755007855234_ts1755007855255;
                // END: non_ansi_concat_port_ts1755007855256

                // BEGIN: primitive_example_ts1755007855249
                and (inj_o_p_and_1755007855249_328, inj_cond_1755007855191_557, inj_concat_port_output_1755007855234_948_ts1755007855234);
                xor (inj_o_p_xor_1755007855249_129, inj_cond_1755007855191_557, inj_concat_port_output_1755007855234_948_ts1755007855234);
                // END: primitive_example_ts1755007855249

                // BEGIN: mod_case_standard_ts1755007855242
            always_comb begin
                case (inj_in_cmd_1755007855242_894)
                    8'd0, 8'd1, 8'd2: begin
                        inj_out_status_1755007855242_318 = 4'hA;
                    end
                    8'd3, 8'd4: begin
                        inj_out_status_1755007855242_318 = 4'hB;
                    end
                    default: begin
                        inj_out_status_1755007855242_318 = 4'hF;
                    end
                endcase
            end
                // END: mod_case_standard_ts1755007855242

                // BEGIN: simple_assign_ts1755007855237
                assign inj_out_1755007855237_443 = inj_op2_u_1755007855191_345;
                // END: simple_assign_ts1755007855237

            assign inj_non_ansi_i_1755007855234_221_ts1755007855234 = 2'b10;
            assign inj_non_ansi_j_1755007855234_290_ts1755007855234 = 2'b01;
            assign inj_concat_port_output_1755007855234_948_ts1755007855234 = inj_cond_1755007855191_557_ts1755007855234;
            // END: non_ansi_concat_port_ts1755007855234

            attributes_test attributes_test_inst_1755007855231_3933 (
                .i_attr_in(inj_cond_1755007855191_557),
                .o_attr_out(inj_o_attr_out_1755007855231_347)
            );
            // BEGIN: mod_simple_ts1755007855228
            assign inj_out_1755007855228_420 = internal_w_ts1755007855211;
            // END: mod_simple_ts1755007855228

            // BEGIN: child_concat_output_ts1755007855226
            assign inj_data_1755007855225_229 = inj_cond_1755007855191_557 ? 8'hAA : 8'h55;
            // END: child_concat_output_ts1755007855226

            split_multiple_blocking split_multiple_blocking_inst_1755007855223_3940 (
                .data_in_n(inj_a_1755007855195_44),
                .data_out1_n(inj_data_out1_n_1755007855223_796),
                .data_out2_n(inj_data_out2_n_1755007855223_898)
            );
            sub_inst_array_mod sub_inst_array_mod_inst_1755007855220_5892 (
                .in(inj_i3_r_1755007855194_135),
                .out(inj_out_1755007855220_404)
            );
            // BEGIN: cu_base_ts1755007855217
            assign inj_data_out_1755007855217_528 = data_b_ts1755007855202;
            // END: cu_base_ts1755007855217

            // BEGIN: range_select_simple_packed_ts1755007855213
            assign inj_out_slice_be_1755007855213_256 = inj_in_vec_1755007855213_769[7:0]; 
            assign inj_out_slice_le_1755007855213_263 = inj_in_vec_1755007855213_769[7:0]; 
            // END: range_select_simple_packed_ts1755007855213

        assign internal_w_ts1755007855211 = inj_cond_1755007855191_557;
        assign inj_dout_1755007855211_364       = internal_w_ts1755007855211;
        // END: ContinuousWire_ts1755007855211

        // BEGIN: LintAsyncFovIssue_ts1755007855208
        always_ff @(posedge clk or negedge reset) begin
            if (!reset) begin
                inj_out_i_1755007855208_500 <= 1'b0;
            end else begin
                inj_out_i_1755007855208_500 <= inj_cond_1755007855191_557 & inj_out_i_1755007855208_500;
            end
        end
        // END: LintAsyncFovIssue_ts1755007855208

        // BEGIN: used_before_declared_diag_mod_ts1755007855206
        logic [7:0] undeclared_var_ubddm = 8'd5;
        assign inj_out_val_1755007855206_926 = inj_i3_r_1755007855194_135 + undeclared_var_ubddm;
        // END: used_before_declared_diag_mod_ts1755007855206

        module_assign_nonblocking module_assign_nonblocking_inst_1755007855204_8924 (
            .reset(reset),
            .out_data_q(inj_out_data_q_1755007855204_729),
            .clk(clk),
            .in_value(data_b_ts1755007855202)
        );
    task automatic modify_vars;
        input logic [7:0] task_arg_ts1755007855202;
        logic [7:0] task_local_ts1755007855202 ;
        begin
            task_local_ts1755007855202 = task_arg_ts1755007855202;
            data_a_ts1755007855202 = task_local_ts1755007855202 + 8'd1;
            data_b_ts1755007855202 = task_arg_ts1755007855202 - 8'd1;
        end
    endtask
    always_comb begin
        if (inj_cond_1755007855191_557) begin
            data_a_ts1755007855202 = inj_i3_r_1755007855194_135;
            data_b_ts1755007855202 = 8'hFF;
            modify_vars(inj_op2_u_1755007855191_345);
        end else begin
            data_a_ts1755007855202 = 8'h00;
            data_b_ts1755007855202 = 8'h00;
        end
    end
    always_comb begin
        inj_data_a_out_task_1755007855201_742 = data_a_ts1755007855202 + 8'd2;
        inj_data_b_out_task_1755007855201_729 = data_b_ts1755007855202;
    end
    // END: module_task_args_ts1755007855202

    target_module_for_bind target_module_for_bind_inst_1755007855200_4279 (
        .o_target_result(inj_o_target_result_1755007855200_227),
        .i_target_clk(clk),
        .i_target_data(inj_op2_u_1755007855191_345)
    );
    AlwaysCombInvert AlwaysCombInvert_inst_1755007855199_2312 (
        .a(inj_a_1755007855195_44),
        .y(inj_y_1755007855199_646)
    );
    always @(posedge clk) begin
        inj_out1_f_1755007855197_304 <= inj_op1_u_1755007855191_882;
        inj_out2_f_1755007855197_944 <= inj_op2_u_1755007855191_345;
        inj_out3_f_1755007855197_889 <= inj_i3_r_1755007855194_135;
    end
    // END: split_independent_nb_ts1755007855198

    casez_xz casez_xz_inst_1755007855196_7880 (
        .out_res(inj_out_res_1755007855196_852),
        .in_val(inj_in_val_1755007855196_259)
    );
    range_select_indexed_packed range_select_indexed_packed_inst_1755007855195_1936 (
        .width(inj_in_val_1755007855192_813),
        .out_down(inj_out_down_1755007855195_853),
        .out_up(inj_out_up_1755007855195_391),
        .in_vec(inj_in2_1755007855191_583),
        .start_index(inj_start_index_1755007855195_319)
    );
    AlwaysCombInvert AlwaysCombInvert_inst_1755007855195_1545 (
        .y(inj_y_1755007855195_216),
        .a(inj_a_1755007855195_44)
    );
    split_complex_blocking split_complex_blocking_inst_1755007855194_1264 (
        .o2_r(inj_o2_r_1755007855194_103),
        .o3_r(inj_o3_r_1755007855194_808),
        .i1_r(inj_op2_u_1755007855191_345),
        .i2_r(inj_op1_u_1755007855191_882),
        .i3_r(inj_i3_r_1755007855194_135),
        .o1_r(inj_o1_r_1755007855194_957)
    );
    always @(posedge clk) begin
        if (inj_cond_1755007855191_557) begin
            inj_out_vec_y_1755007855193_114[3:0] <= inj_op2_u_1755007855191_345[3:0];
            inj_out_vec_y_1755007855193_114[7:4] <= inj_op2_u_1755007855191_345[7:4] + 1;
        end else begin
            inj_out_vec_y_1755007855193_114 <= 8'hFF;
        end
    end
    // END: split_vector_assign_ts1755007855193

    unknown_class_pkg_diag_mod unknown_class_pkg_diag_mod_inst_1755007855192_4148 (
        .in_val(inj_in_val_1755007855192_813),
        .out_val(inj_out_val_1755007855192_937)
    );
    always @(*) begin
        inj_sum_u_1755007855191_290 = inj_op1_u_1755007855191_882 + inj_op2_u_1755007855191_345;
        inj_diff_u_1755007855191_648 = inj_op1_u_1755007855191_882 - inj_op2_u_1755007855191_345;
        inj_prod_u_1755007855191_724 = inj_op1_u_1755007855191_882 * inj_op2_u_1755007855191_345;
    end
    // END: split_arith_blocking_ts1755007855191

    always_comb_if always_comb_if_inst_1755007855191_3431 (
        .cond(inj_cond_1755007855191_557),
        .in1(inj_in1_1755007855191_835),
        .in2(inj_in2_1755007855191_583),
        .out(inj_out_1755007855191_11)
    );
    module_selection module_selection_inst_1755007855191_8737 (
        .in_index(inj_in_index_1755007855191_50),
        .in_part_lsb(inj_in_part_lsb_1755007855191_337),
        .in_vector(inj_in_vector_1755007855191_276),
        .out_bit_select(inj_out_bit_select_1755007855191_748),
        .out_bitwise_ops(inj_out_bitwise_ops_1755007855191_649),
        .out_part_select(inj_out_part_select_1755007855191_193),
        .out_vector_assign(inj_out_vector_assign_1755007855191_807),
        .in_bit(clk)
    );
endmodule

