interface simple_if (
    input logic clk
);
    logic data;
    logic ready;
    modport master (output data, input ready);
    modport slave (input data, output ready);
endinterface
module HandleOutOfBoundsRead (
    input logic [3:0] i_addr_arr,
    input logic [3:0] i_addr_sel,
    input logic [7:0] i_vector,
    output logic [7:0] o_array_var_elem,
    output logic o_sel_var_bit
);
    parameter ARR_SIZE = 4;
    logic [7:0] my_array [0:ARR_SIZE-1];
    assign my_array[0] = 8'd10;
    assign my_array[1] = 8'd20;
    assign my_array[2] = 8'd30;
    assign my_array[3] = 8'd40;
    assign o_sel_var_bit = i_vector[i_addr_sel];
    assign o_array_var_elem = my_array[i_addr_arr];
endmodule

module deep_logic (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    output logic [7:0] out
);
    assign out = (((a & b) | (~c)) ^ (a + b)) - (c << 2);
endmodule

module module_with_params #(
    parameter integer DATA_WIDTH = 8
) (
    input wire [7:0] param_in,
    output wire [7:0] param_out
);
    assign param_out = param_in;
endmodule

module sub_module (
    input logic sub_in,
    output logic sub_out
);
    assign sub_out = !sub_in;
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_a_1755007757675_348,
    input logic [7:0] inj_b_1755007757675_40,
    input logic [7:0] inj_c_1755007757675_655,
    input logic inj_din_a_1755007757675_672,
    input logic inj_din_b_1755007757675_834,
    input logic [3:0] inj_i_addr_arr_1755007757676_336,
    input logic [3:0] inj_i_addr_sel_1755007757676_182,
    input logic [15:0] inj_in1_1755007757682_232,
    input logic [15:0] inj_in2_1755007757682_208,
    input logic [15:0] inj_in3_1755007757682_192,
    input logic [15:0] inj_in4_1755007757682_345,
    input logic [15:0] inj_in5_1755007757682_495,
    input wire [7:0] inj_in_func_a_1755007757676_694,
    input wire [7:0] inj_in_func_b_1755007757676_260,
    input logic [31:0] inj_nested_in_1755007757687_407,
    input wire reset,
    output logic inj_and_reduce_1755007757684_193,
    output logic [7:0] inj_data_1755007757686_507,
    output logic inj_dout_a_1755007757675_684,
    output logic inj_dout_b_1755007757675_138,
    output logic inj_dummy_1755007757689_237,
    output logic [7:0] inj_inner_field_o_1755007757687_745,
    output logic [4:0] inj_internal_out_1755007757677_442,
    output logic inj_main_out_1755007757678_139,
    output logic [7:0] inj_o_array_var_elem_1755007757676_696,
    output logic inj_o_bind_status_1755007757677_348,
    output logic inj_o_sel_var_bit_1755007757676_757,
    output logic inj_or_reduce_1755007757684_6,
    output logic [7:0] inj_out1_1755007757691_756,
    output logic [7:0] inj_out2_1755007757691_241,
    output logic [7:0] inj_out_1755007757675_287,
    output logic inj_out_1755007757682_318,
    output logic [7:0] inj_out_func_result_1755007757676_766,
    output wire [7:0] inj_param_out_1755007757679_689,
    output logic [7:0] inj_result_m_1755007757680_197,
    output logic inj_xor_reduce_1755007757684_144
);
    // BEGIN: ModMultipleAlways_ts1755007757675
    // BEGIN: module_function_ts1755007757676
    function automatic [7:0] add_and_subtract;
    input [7:0] val1;
    input [7:0] val2;
    reg [7:0] temp_ts1755007757676;
        // BEGIN: always_multi_stmt_unhandled_ts1755007757691
        always_comb begin
            inj_out1_1755007757691_756 = inj_c_1755007757675_655;
            inj_out2_1755007757691_241 = inj_a_1755007757675_348;
        end
        // END: always_multi_stmt_unhandled_ts1755007757691

        // BEGIN: mod_err_event_constant_ts1755007757690
        always @(posedge 1'b1) begin
            inj_dummy_1755007757689_237 = ~inj_dummy_1755007757689_237;
        end
        // END: mod_err_event_constant_ts1755007757690

        // BEGIN: nested_types_mod_ts1755007757688
        typedef struct packed {
            logic [7:0] inner_field_ts1755007757688;
            logic [7:0] padding_ts1755007757688;
        } inner_struct_t;
        typedef union packed {
            logic [31:0] full_word_ts1755007757688;
            struct packed {
                logic [15:0] unused_ts1755007757688;
                inner_struct_t inner_data;
            } outer_fields;
        } outer_union_t;
        outer_union_t nested_var;
        always_comb begin
            nested_var.full_word_ts1755007757688 = inj_nested_in_1755007757687_407;
        end
        assign inj_inner_field_o_1755007757687_745 = nested_var.outer_fields.inner_data.inner_field_ts1755007757688;
        // END: nested_types_mod_ts1755007757688

        // BEGIN: child_concat_output_ts1755007757686
        assign inj_data_1755007757686_507 = inj_din_a_1755007757675_672 ? 8'hAA : 8'h55;
        // END: child_concat_output_ts1755007757686

        // BEGIN: ReductionOperations_ts1755007757684
        assign inj_and_reduce_1755007757684_193 = &inj_b_1755007757675_40;
        assign inj_or_reduce_1755007757684_6 = |inj_b_1755007757675_40;
        assign inj_xor_reduce_1755007757684_144 = ^inj_b_1755007757675_40;
        // END: ReductionOperations_ts1755007757684

        // BEGIN: arith_comp_ops_ts1755007757682
        assign inj_out_1755007757682_318 = (inj_in1_1755007757682_232 + inj_in2_1755007757682_208) * inj_in3_1755007757682_192 > inj_in4_1755007757682_345 - inj_in5_1755007757682_495;
        // END: arith_comp_ops_ts1755007757682

        // BEGIN: split_nested_if_ts1755007757680
        always @(posedge clk) begin
            if (inj_din_b_1755007757675_834) begin
                if (inj_din_a_1755007757675_672) begin
                    inj_result_m_1755007757680_197 <= inj_b_1755007757675_40;
                end else begin
                    inj_result_m_1755007757680_197 <= inj_a_1755007757675_348;
                end
            end else begin
                inj_result_m_1755007757680_197 <= inj_c_1755007757675_655;
            end
        end
        // END: split_nested_if_ts1755007757680

        module_with_params module_with_params_inst_1755007757679_4912 (
            .param_in(inj_in_func_a_1755007757676_694),
            .param_out(inj_param_out_1755007757679_689)
        );
        // BEGIN: hierarchy_if_ts1755007757678
        sub_module u_sub (
            .sub_in(inj_din_b_1755007757675_834),
            .sub_out(inj_main_out_1755007757678_139)
        );
        simple_if if_inst (.clk(clk));
        always_comb begin
            if_inst.data = inj_din_b_1755007757675_834;
            if_inst.ready = inj_main_out_1755007757678_139;
        end
        // END: hierarchy_if_ts1755007757678

        // BEGIN: case_parallel_simple_mod_ts1755007757677
        always @* begin
            (* parallel *)
            case (inj_i_addr_arr_1755007757676_336)
                4'd0, 4'd1: inj_internal_out_1755007757677_442 = 14;
                4'd2, 4'd3: inj_internal_out_1755007757677_442 = 15;
                default: inj_internal_out_1755007757677_442 = 18;
            endcase
        end
        // END: case_parallel_simple_mod_ts1755007757677

        // BEGIN: module_to_bind_ts1755007757677
        always_comb inj_o_bind_status_1755007757677_348 = |inj_i_addr_arr_1755007757676_336;
        // END: module_to_bind_ts1755007757677

        HandleOutOfBoundsRead HandleOutOfBoundsRead_inst_1755007757676_3131 (
            .o_array_var_elem(inj_o_array_var_elem_1755007757676_696),
            .o_sel_var_bit(inj_o_sel_var_bit_1755007757676_757),
            .i_addr_arr(inj_i_addr_arr_1755007757676_336),
            .i_addr_sel(inj_i_addr_sel_1755007757676_182),
            .i_vector(inj_a_1755007757675_348)
        );
    begin
    temp_ts1755007757676 = val1 + val2;
    add_and_subtract = temp_ts1755007757676 - 1;
    end
    endfunction
    always_comb begin
    inj_out_func_result_1755007757676_766 = add_and_subtract(inj_in_func_a_1755007757676_694, inj_in_func_b_1755007757676_260);
    end
    // END: module_function_ts1755007757676

    deep_logic deep_logic_inst_1755007757675_9086 (
        .c(inj_c_1755007757675_655),
        .out(inj_out_1755007757675_287),
        .a(inj_a_1755007757675_348),
        .b(inj_b_1755007757675_40)
    );
    always @(posedge clk or negedge reset) begin 
    if (!reset) begin 
        inj_dout_a_1755007757675_684 <= 1'b0;
    end else begin
        inj_dout_a_1755007757675_684 <= inj_din_a_1755007757675_672; 
    end
    end
    always @(posedge clk) begin 
    inj_dout_b_1755007757675_138 <= inj_din_b_1755007757675_834; 
    end
    // END: ModMultipleAlways_ts1755007757675
endmodule

