interface seq2_if;
    logic [7:0] status_byte;
    modport PortB (output status_byte);
endinterface
interface seq_if;
    logic [31:0] value_a;
    modport PortA (output value_a);
endinterface
module ArrayIndexAndPartSelect (
    input logic [31:0] data_in,
    input int index_in,
    input logic [4:0] start_bit,
    output logic bit_out,
    output logic [7:0] byte_out
);
    logic [31:0] internal_data = data_in;
    assign bit_out = internal_data[index_in];
    assign byte_out = internal_data[start_bit +: 8];
endmodule

module CaseStatementConditions (
    input wire [3:0] data_c,
    input wire [1:0] selector,
    output logic [3:0] out_case_case,
    output logic [3:0] out_case_casex,
    output logic [3:0] out_case_casez
);
    always_comb begin
        case (selector)
            2'b00: out_case_case = data_c;
            2'b01: out_case_case = data_c + 1;
            2'b10: out_case_case = data_c + 2;
            default: out_case_case = 4'bxxxx;
        endcase
        casez (selector)
            2'b0?: out_case_casez = data_c + 10;
            2'b1?: out_case_casez = data_c + 20;
            default: out_case_casez = 4'bzzzz;
        endcase
        casex (selector)
            2'b0?: out_case_casex = data_c - 1;
            2'b1?: out_case_casex = data_c - 2;
            default: out_case_casex = 4'bxxxx;
        endcase
    end
endmodule

module LintImplicitWidth (
    input logic [7:0] in_wide,
    output logic [3:0] out_narrow
);
    assign out_narrow = in_wide;
endmodule

module LintLatch (
    input logic in_j,
    input logic in_k,
    output logic out_l
);
    always_comb begin
        if (in_j) begin
            out_l = in_k;
        end else begin
            out_l = 1'b0; 
        end
    end
endmodule

module LogicDependencyChain (
    input logic clk,
    input logic d_in,
    output logic q_out
);
    logic q1, q2;
    always @(posedge clk) begin
        q1 <= d_in;
    end
    always @(q1) begin
        q2 = ~q1;
    end
    assign q_out = q2;
endmodule

module ModClockedConditional (
    input logic clk,
    input logic data_in,
    input logic enable,
    output logic data_out
);
    logic reg_data;
    always @(posedge clk) begin
    if (enable) begin
        reg_data <= data_in;
    end
    end
    assign data_out = reg_data;
endmodule

module ModRegister (
    input logic din,
    output logic dout
);
    always @* begin
        dout = din;
    end
endmodule

module ProgramDefinition (
    input wire in_pd,
    output logic out_pd
);
    assign out_pd = in_pd;
endmodule

module case_basic (
    input logic [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b00: out_res = 1'b0;
            2'b01: out_res = 1'b1;
            2'b10: out_res = 1'b0;
            2'b11: out_res = 1'b1;
        endcase
    end
endmodule

module case_single_default_after_item (
    input logic [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b01: out_res = 1'b1;
            default: out_res = 1'b0;
            2'b10: out_res = 1'b1;
        endcase
    end
endmodule

module deep_task_logic (
    input wire [1:0] dtl_action_sel,
    input wire dtl_clk,
    input wire [7:0] dtl_data_a,
    input wire [7:0] dtl_data_b,
    input wire dtl_en,
    input wire dtl_rst_n,
    output logic [7:0] dtl_result_reg
);
    task automatic perform_action;
        input [7:0] in_a;
        input [7:0] in_b;
        input [1:0] action;
        output logic [7:0] calculated_res;
        logic [7:0] temp_task_calc;
        if (action[0]) begin
            if (action[1]) begin
                temp_task_calc = in_a + in_b;
            end else begin
                temp_task_calc = in_a - in_b;
            end
        end else begin
            if (action[1]) begin
                temp_task_calc = in_a & in_b;
            end else begin
                temp_task_calc = in_a | in_b;
            end
        end
        case (temp_task_calc[1:0])
            2'b00: calculated_res = temp_task_calc ^ 8'hFF;
            2'b01: calculated_res = temp_task_calc + 1;
            2'b10: calculated_res = temp_task_calc - 1;
            default: calculated_res = temp_task_calc;
        endcase
    endtask
    always_ff @(posedge dtl_clk or negedge dtl_rst_n) begin
        if (!dtl_rst_n) begin
            dtl_result_reg <= 8'd0;
        end else begin
            logic [7:0] next_dtl_result;
            if (dtl_en) begin
                perform_action(dtl_data_a, dtl_data_b, dtl_action_sel, next_dtl_result);
            end else begin
                next_dtl_result = dtl_result_reg;
            end
            dtl_result_reg <= next_dtl_result;
        end
    end
endmodule

module element_select_packed (
    input logic [7:0] in_vec,
    input int index_in,
    output logic out_bit,
    output logic [3:0] out_slice
);
    always_comb begin
        if (index_in >= 0 && index_in < 8)
            out_bit = in_vec[index_in];
        else
            out_bit = 'x; 
    end
    assign out_slice = in_vec[6:3];
endmodule

module invalid_this_diag_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module loop_with_internal_assign (
    input logic [3:0] start_val,
    output logic [7:0] final_val
);
    logic [7:0] current_val;
    always_comb begin
        current_val = start_val;
        for (int k = 0; k < 3; k = k + 1) begin
            current_val = current_val + 1;
        end
        final_val = current_val;
    end
endmodule

module mod_casez_wildcard (
    input bit [3:0] in_mask_z,
    output bit [1:0] out_match_type_z
);
always_comb begin
    casez (in_mask_z)
        4'b10?0: begin
            out_match_type_z = 2'b00;
        end
        4'b011?: begin
            out_match_type_z = 2'b01;
        end
        default: begin
            out_match_type_z = 2'b11;
        end
    endcase
end
endmodule

module mod_event_implicit (
    input wire [3:0] data_in,
    output reg [3:0] data_out
);
    always @* begin
        data_out = data_in;
    end
endmodule

module mod_split_comb (
    input logic [7:0] data_in,
    input logic enable,
    output logic [7:0] out_a,
    output logic [7:0] out_b
);
    logic [7:0]  split_comb_var;
    logic [7:0] other_comb_var;
    always_comb begin
        split_comb_var = 8'b0; 
        other_comb_var = 8'b0;
        if (enable) begin
            split_comb_var = data_in;
            other_comb_var = data_in + 1;
        end
        out_a = split_comb_var;
        out_b = other_comb_var;
    end
endmodule

module module_bitfield_concat (
    input logic [7:0] input_bf,
    input logic [3:0] input_bf_slice,
    output logic [7:0] output_bf,
    output logic [3:0] output_bf_slice
);
    logic [7:0] my_bitfield ;
    always_comb begin
        if (input_bf[7]) begin
            my_bitfield = input_bf;
        end else begin
            my_bitfield = {input_bf[0], input_bf[7:1]};
        end
        my_bitfield[3:0] = input_bf_slice;
    end
    assign output_bf = my_bitfield;
    assign output_bf_slice = my_bitfield[3:0];
endmodule

module module_in_program_ref (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module sequential_register (
    input logic clk,
    input logic data_in,
    input logic enable_in,
    input logic reset_n,
    output logic data_out
);
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            data_out <= 1'b0; 
        end else if (enable_in) begin
            data_out <= data_in; 
        end
    end
endmodule

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module simple_comb (
    input wire [7:0] in_data,
    output wire [7:0] out_data
);
    wire [7:0] intermediate_a;
    wire [7:0] intermediate_b;
    wire [7:0] intermediate_c;
    assign intermediate_a = in_data + 8'd1;
    assign intermediate_b = intermediate_a << 1;
    assign intermediate_c = intermediate_a >> 1;
    assign out_data = intermediate_b | intermediate_c;
endmodule

module wide_bus_ops (
    input wire [63:0] wide_a,
    input wire [63:0] wide_b,
    output wire [127:0] concat_out,
    output wire [7:0] reduce_xor_out,
    output wire [63:0] wide_sum
);
    assign wide_sum = wide_a + wide_b;
    assign reduce_xor_out = ^wide_a[63:0];
    assign concat_out = {wide_a, wide_b};
endmodule

module snippet #(
    parameter int WIDTH = 8
) (
    input wire clk,
    input logic inj_b_1755007906248_424,
    input logic [3:0] inj_case_inside_val_1755007906285_362,
    input wire [3:0] inj_data_c_1755007906272_837,
    input logic [31:0] inj_data_in_1755007906244_876,
    input logic [7:0] inj_data_in_1755007906244_898,
    input wire [7:0] inj_dtl_data_b_1755007906277_976,
    input bit inj_enable_in_1755007906247_606,
    input logic [7:0] inj_i2_s_1755007906262_68,
    input logic [7:0] inj_i3_s_1755007906262_540,
    input logic [3:0] inj_i_addr_sel_1755007906309_632,
    input wire [7:0] inj_in_data_1755007906260_145,
    input bit [3:0] inj_in_mask_z_1755007906244_886,
    input logic [1:0] inj_in_val_1755007906253_59,
    input int inj_index_in_1755007906244_141,
    input wire [1:0] inj_selector_1755007906272_277,
    input logic [4:0] inj_start_bit_1755007906244_488,
    input logic inj_task_in_1755007906243_409,
    input wire [63:0] inj_wide_a_1755007906243_97,
    input wire [63:0] inj_wide_b_1755007906243_535,
    input wire reset,
    output logic inj_bit_out_1755007906244_911,
    output logic [7:0] inj_byte_out_1755007906244_368,
    output wire [127:0] inj_concat_out_1755007906243_25,
    output int inj_config_data_out_1755007906258_936,
    output logic inj_data_out_1755007906255_554,
    output reg [3:0] inj_data_out_1755007906294_500,
    output logic inj_data_out_1755007906299_99,
    output int inj_data_out_1755007906397_928,
    output logic [31:0] inj_data_out_w_1755007906280_680,
    output logic inj_dout_1755007906289_109,
    output logic inj_dout_1755007906404_89,
    output int inj_driven_var_1755007906245_817,
    output logic [7:0] inj_dtl_result_reg_1755007906277_244,
    output logic [7:0] inj_final_val_1755007906315_159,
    output logic inj_fs_out_target_1755007906245_993,
    output logic [4:0] inj_internal_out_1755007906285_805,
    output logic [4:0] inj_internal_out_1755007906421_438,
    output reg inj_non_ansi_b_1755007906249_321,
    output logic inj_non_ansi_basic_output_1755007906249_398,
    output logic [7:0] inj_o1_s_1755007906262_117,
    output logic [7:0] inj_o2_s_1755007906262_156,
    output logic [7:0] inj_o3_s_1755007906262_426,
    output logic [7:0] inj_o_array_var_elem_1755007906309_788,
    output logic inj_o_out_1755007906327_872,
    output logic [7:0] inj_o_out_1755007906373_767,
    output logic inj_o_sel_var_bit_1755007906309_534,
    output logic [7:0] inj_out1_f_1755007906389_716,
    output logic [7:0] inj_out1_f_1755007906438_715,
    output logic [7:0] inj_out2_f_1755007906389_426,
    output logic [7:0] inj_out2_f_1755007906438_205,
    output logic [7:0] inj_out3_f_1755007906389_221,
    output logic [7:0] inj_out3_f_1755007906438_480,
    output bit inj_out_1755007906247_294,
    output logic [7:0] inj_out_1755007906429_941,
    output logic [7:0] inj_out_a_1755007906244_149,
    output logic [7:0] inj_out_b_1755007906244_456,
    output logic inj_out_bit_1755007906321_599,
    output logic [3:0] inj_out_case_case_1755007906272_235,
    output logic [3:0] inj_out_case_casex_1755007906272_919,
    output logic [3:0] inj_out_case_casez_1755007906272_739,
    output wire [7:0] inj_out_data_1755007906260_201,
    output wire [3:0] inj_out_element_1755007906275_450,
    output logic inj_out_g_1755007906252_965,
    output logic inj_out_l_1755007906264_50,
    output bit [1:0] inj_out_match_type_x_1755007906344_399,
    output bit [1:0] inj_out_match_type_z_1755007906244_359,
    output logic [3:0] inj_out_narrow_1755007906251_356,
    output logic inj_out_pd_1755007906413_791,
    output reg inj_out_res_1755007906253_176,
    output reg inj_out_res_1755007906256_791,
    output reg inj_out_res_1755007906381_32,
    output logic [3:0] inj_out_slice_1755007906321_586,
    output int inj_out_val_1755007906246_71,
    output int inj_out_val_1755007906250_332,
    output int inj_out_val_1755007906359_212,
    output logic [7:0] inj_out_val_o_1755007906268_248,
    output logic [7:0] inj_output_bf_1755007906338_997,
    output logic [7:0] inj_output_bf_1755007906365_444,
    output logic [3:0] inj_output_bf_slice_1755007906338_21,
    output logic [3:0] inj_output_bf_slice_1755007906365_836,
    output logic inj_q_out_1755007906283_410,
    output wire [7:0] inj_reduce_xor_out_1755007906243_128,
    output logic inj_sequence_valid_1755007906351_369,
    output logic inj_sub_out_1755007906266_517,
    output logic inj_sum_1755007906332_535,
    output logic inj_task_out_1755007906243_441,
    output wire [63:0] inj_wide_sum_1755007906243_508,
    output logic inj_y_1755007906248_172,
    output logic [3:0] inj_y_1755007906304_937
);
    // BEGIN: task_example_ts1755007906243
    task automatic process_data (input logic data);
        logic temp_ts1755007906243;
        temp_ts1755007906243 = data; 
    // BEGIN: m_driver_check_ts1755007906245
    int my_driven_var_ts1755007906245;
    function automatic void write_to_var(input int val);
        my_driven_var_ts1755007906245 = val;
    // BEGIN: non_ansi_basic_ts1755007906249
    input wire clk_ts1755007906249;
    output reg inj_non_ansi_b_1755007906249_321_ts1755007906249;
    input logic inj_task_in_1755007906243_409_ts1755007906249;
    output logic inj_non_ansi_basic_output_1755007906249_398_ts1755007906249;
    // BEGIN: split_complex_nb_ts1755007906262
    logic [7:0] t1_s_ts1755007906262, t2_s_ts1755007906262;
    // BEGIN: unpacked_array_module_ts1755007906275
    logic [3:0] data_array_ts1755007906275 [4];
    // BEGIN: HandleOutOfBoundsRead_ts1755007906309
    parameter ARR_SIZE = 4;
    logic [7:0] my_array_ts1755007906309 [0:ARR_SIZE-1];
    // BEGIN: attributes_on_expr_port_ts1755007906327
    logic internal_sig_ts1755007906327;
    // BEGIN: module_bitfield_concat_ts1755007906366
    logic [7:0] my_bitfield_ts1755007906366 ;
    // BEGIN: mod_module_attrs_ts1755007906373
    logic [WIDTH-1:0] r_data_ts1755007906373;
    // BEGIN: split_independent_nb_ts1755007906439
    always @(posedge clk) begin
        inj_out1_f_1755007906438_715 <= inj_data_in_1755007906244_898;
        inj_out2_f_1755007906438_205 <= inj_i3_s_1755007906262_540;
        inj_out3_f_1755007906438_480 <= inj_i2_s_1755007906262_68;
    end
    // END: split_independent_nb_ts1755007906439

    // BEGIN: deep_logic_ts1755007906429
    assign inj_out_1755007906429_941 = (((inj_data_in_1755007906244_898 & inj_i2_s_1755007906262_68) | (~inj_i3_s_1755007906262_540)) ^ (inj_data_in_1755007906244_898 + inj_i2_s_1755007906262_68)) - (inj_i3_s_1755007906262_540 << 2);
    // END: deep_logic_ts1755007906429

    // BEGIN: case_priority_overlapping_mod_ts1755007906421
    always @* begin
        priority casez (inj_in_val_1755007906253_59)
            2'b1?: inj_internal_out_1755007906421_438 = 5;
            2'b?1: inj_internal_out_1755007906421_438 = 6;  
            2'b0?: inj_internal_out_1755007906421_438 = 7;
            2'b?0: inj_internal_out_1755007906421_438 = 8;  
            default: inj_internal_out_1755007906421_438 = 9;
        endcase
    end
    // END: case_priority_overlapping_mod_ts1755007906421

    ProgramDefinition ProgramDefinition_inst_1755007906413_1064 (
        .in_pd(reset),
        .out_pd(inj_out_pd_1755007906413_791)
    );
    ModRegister ModRegister_inst_1755007906404_3816 (
        .din(inj_b_1755007906248_424),
        .dout(inj_dout_1755007906404_89)
    );
    // BEGIN: mod_named_begin_ts1755007906397
    always_comb begin : my_named_block
        inj_data_out_1755007906397_928 = inj_index_in_1755007906244_141;
    end
    // END: mod_named_begin_ts1755007906397

    // BEGIN: split_independent_nb_ts1755007906389
    always @(posedge clk) begin
        inj_out1_f_1755007906389_716 <= inj_i3_s_1755007906262_540;
        inj_out2_f_1755007906389_426 <= inj_i2_s_1755007906262_68;
        inj_out3_f_1755007906389_221 <= inj_data_in_1755007906244_898;
    end
    // END: split_independent_nb_ts1755007906389

    case_single_default_after_item case_single_default_after_item_inst_1755007906381_7159 (
        .out_res(inj_out_res_1755007906381_32),
        .in_val(inj_in_val_1755007906253_59)
    );
    always_comb begin
        r_data_ts1755007906373 = inj_dtl_data_b_1755007906277_976;
    end
    assign inj_o_out_1755007906373_767 = r_data_ts1755007906373;
    // END: mod_module_attrs_ts1755007906373

    always_comb begin
        if (inj_i2_s_1755007906262_68[7]) begin
            my_bitfield_ts1755007906366 = inj_i2_s_1755007906262_68;
        end else begin
            my_bitfield_ts1755007906366 = {inj_i2_s_1755007906262_68[0], inj_i2_s_1755007906262_68[7:1]};
        end
        my_bitfield_ts1755007906366[3:0] = inj_case_inside_val_1755007906285_362;
    end
    assign inj_output_bf_1755007906365_444 = my_bitfield_ts1755007906366;
    assign inj_output_bf_slice_1755007906365_836 = my_bitfield_ts1755007906366[3:0];
    // END: module_bitfield_concat_ts1755007906366

    module_in_program_ref module_in_program_ref_inst_1755007906359_9523 (
        .out_val(inj_out_val_1755007906359_212),
        .in_val(inj_index_in_1755007906244_141)
    );
    // BEGIN: module_sequence_different_if_ts1755007906352
    seq_if sif_port();
    seq2_if sif2_port();
    always_comb begin
        sif_port.value_a = inj_data_in_1755007906244_876;
        sif2_port.status_byte = inj_i3_s_1755007906262_540;
        inj_sequence_valid_1755007906351_369 = 1'b1;
    end
    // END: module_sequence_different_if_ts1755007906352

    // BEGIN: mod_casex_wildcard_overlap_priority_ts1755007906344
always_comb begin
    inj_out_match_type_x_1755007906344_399 = 2'b01;
    priority casex (inj_in_mask_z_1755007906244_886)
        4'b1X0Z: begin
            inj_out_match_type_x_1755007906344_399 = 2'b10;
        end
        4'b10?Z: begin
            inj_out_match_type_x_1755007906344_399 = 2'b11;
        end
        4'bZ1?X: begin
            inj_out_match_type_x_1755007906344_399 = 2'b00;
        end
        default: begin
            inj_out_match_type_x_1755007906344_399 = 2'b01;
        end
    endcase
end
    // END: mod_casex_wildcard_overlap_priority_ts1755007906344

    module_bitfield_concat module_bitfield_concat_inst_1755007906338_2715 (
        .output_bf_slice(inj_output_bf_slice_1755007906338_21),
        .input_bf(inj_data_in_1755007906244_898),
        .input_bf_slice(inj_case_inside_val_1755007906285_362),
        .output_bf(inj_output_bf_1755007906338_997)
    );
    simple_adder simple_adder_inst_1755007906332_9088 (
        .sum(inj_sum_1755007906332_535),
        .a(inj_b_1755007906248_424),
        .b(inj_task_in_1755007906243_409)
    );
    assign internal_sig_ts1755007906327 = inj_b_1755007906248_424 & inj_task_in_1755007906243_409;
    simple_adder sa_inst(
        .a  (inj_b_1755007906248_424),
        (* fanout_limit = 10 *) .b(inj_task_in_1755007906243_409),
        .sum(inj_o_out_1755007906327_872)
    );
    // END: attributes_on_expr_port_ts1755007906327

    element_select_packed element_select_packed_inst_1755007906321_282 (
        .out_bit(inj_out_bit_1755007906321_599),
        .out_slice(inj_out_slice_1755007906321_586),
        .in_vec(inj_i3_s_1755007906262_540),
        .index_in(inj_index_in_1755007906244_141)
    );
    loop_with_internal_assign loop_with_internal_assign_inst_1755007906315_2224 (
        .start_val(inj_i_addr_sel_1755007906309_632),
        .final_val(inj_final_val_1755007906315_159)
    );
    assign my_array_ts1755007906309[0] = 8'd10;
    assign my_array_ts1755007906309[1] = 8'd20;
    assign my_array_ts1755007906309[2] = 8'd30;
    assign my_array_ts1755007906309[3] = 8'd40;
    assign inj_o_sel_var_bit_1755007906309_534 = inj_i3_s_1755007906262_540[inj_i_addr_sel_1755007906309_632];
    assign inj_o_array_var_elem_1755007906309_788 = my_array_ts1755007906309[inj_case_inside_val_1755007906285_362];
    // END: HandleOutOfBoundsRead_ts1755007906309

    // BEGIN: AlwaysCombInvert_ts1755007906304
    always_comb inj_y_1755007906304_937 = ~inj_case_inside_val_1755007906285_362;
    // END: AlwaysCombInvert_ts1755007906304

    ModClockedConditional ModClockedConditional_inst_1755007906299_5751 (
        .enable(inj_task_in_1755007906243_409),
        .data_out(inj_data_out_1755007906299_99),
        .clk(clk),
        .data_in(inj_b_1755007906248_424)
    );
    mod_event_implicit mod_event_implicit_inst_1755007906294_5988 (
        .data_in(inj_data_c_1755007906272_837),
        .data_out(inj_data_out_1755007906294_500)
    );
    // BEGIN: ModRegister_ts1755007906289
    always @* begin
        inj_dout_1755007906289_109 = inj_b_1755007906248_424;
    end
    // END: ModRegister_ts1755007906289

    // BEGIN: case_priority_casex_complex_mod_ts1755007906286
    always @* begin
        priority casex ({inj_in_val_1755007906253_59, inj_case_inside_val_1755007906285_362[1:0]})
            4'b1???: inj_internal_out_1755007906285_805 = 24;
            4'b?1??: inj_internal_out_1755007906285_805 = 25;  
            4'b??1?: inj_internal_out_1755007906285_805 = 26;  
            4'b???1: inj_internal_out_1755007906285_805 = 27;  
            4'b0000: inj_internal_out_1755007906285_805 = 28;  
            default: inj_internal_out_1755007906285_805 = 29;
        endcase
    end
    // END: case_priority_casex_complex_mod_ts1755007906286

    LogicDependencyChain LogicDependencyChain_inst_1755007906283_1098 (
        .clk(clk),
        .d_in(inj_b_1755007906248_424),
        .q_out(inj_q_out_1755007906283_410)
    );
    // BEGIN: ModWideBus_ts1755007906280
    assign inj_data_out_w_1755007906280_680 = ~inj_data_in_1755007906244_876;
    // END: ModWideBus_ts1755007906280

    deep_task_logic deep_task_logic_inst_1755007906277_8905 (
        .dtl_en(reset),
        .dtl_rst_n(reset),
        .dtl_result_reg(inj_dtl_result_reg_1755007906277_244),
        .dtl_action_sel(inj_selector_1755007906272_277),
        .dtl_clk(clk),
        .dtl_data_a(inj_in_data_1755007906260_145),
        .dtl_data_b(inj_dtl_data_b_1755007906277_976)
    );
    always @(*) begin
        data_array_ts1755007906275[0] = inj_in_data_1755007906260_145[3:0];
        data_array_ts1755007906275[1] = inj_in_data_1755007906260_145[7:4];
        data_array_ts1755007906275[2] = 4'd8;
        data_array_ts1755007906275[3] = 4'd12;
    end
    assign inj_out_element_1755007906275_450 = data_array_ts1755007906275[inj_selector_1755007906272_277];
    // END: unpacked_array_module_ts1755007906275

    CaseStatementConditions CaseStatementConditions_inst_1755007906272_728 (
        .out_case_casex(inj_out_case_casex_1755007906272_919),
        .data_c(inj_data_c_1755007906272_837),
        .selector(inj_selector_1755007906272_277),
        .out_case_case(inj_out_case_case_1755007906272_235),
        .out_case_casez(inj_out_case_casez_1755007906272_739)
    );
    // BEGIN: split_conditional_blocking_ts1755007906269
    always @(*) begin
        if (inj_task_in_1755007906243_409) begin
            inj_out_val_o_1755007906268_248 = inj_i3_s_1755007906262_540;
        end else begin
            inj_out_val_o_1755007906268_248 = inj_data_in_1755007906244_898;
        end
    end
    // END: split_conditional_blocking_ts1755007906269

    // BEGIN: sub_module_ts1755007906266
    assign inj_sub_out_1755007906266_517 = !inj_task_in_1755007906243_409;
    // END: sub_module_ts1755007906266

    LintLatch LintLatch_inst_1755007906264_9253 (
        .in_j(inj_task_in_1755007906243_409),
        .in_k(inj_b_1755007906248_424),
        .out_l(inj_out_l_1755007906264_50)
    );
    always @(posedge clk) begin
        t1_s_ts1755007906262 <= inj_data_in_1755007906244_898 + inj_i2_s_1755007906262_68;
        inj_o1_s_1755007906262_117 <= t1_s_ts1755007906262 - inj_i3_s_1755007906262_540;
        t2_s_ts1755007906262 <= inj_i2_s_1755007906262_68 * inj_i3_s_1755007906262_540;
        inj_o2_s_1755007906262_156 <= t1_s_ts1755007906262 + t2_s_ts1755007906262;
        inj_o3_s_1755007906262_426 <= t2_s_ts1755007906262 / 2;
    end
    // END: split_complex_nb_ts1755007906262

    simple_comb simple_comb_inst_1755007906260_930 (
        .in_data(inj_in_data_1755007906260_145),
        .out_data(inj_out_data_1755007906260_201)
    );
    // BEGIN: PragmaProtectOptions_ts1755007906258
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
assign inj_config_data_out_1755007906258_936 = inj_index_in_1755007906244_141 + 1;
    // END: PragmaProtectOptions_ts1755007906258

    case_basic case_basic_inst_1755007906256_9152 (
        .in_val(inj_in_val_1755007906253_59),
        .out_res(inj_out_res_1755007906256_791)
    );
    sequential_register sequential_register_inst_1755007906255_5923 (
        .reset_n(reset),
        .data_out(inj_data_out_1755007906255_554),
        .clk(clk),
        .data_in(inj_b_1755007906248_424),
        .enable_in(inj_task_in_1755007906243_409)
    );
    // BEGIN: case_default_ts1755007906254
    always_comb begin
        inj_out_res_1755007906253_176 = 1'b0;
        case (inj_in_val_1755007906253_59)
            2'b01: inj_out_res_1755007906253_176 = 1'b1;
            2'b10: inj_out_res_1755007906253_176 = 1'b0;
            default: inj_out_res_1755007906253_176 = 1'b1;
        endcase
    end
    // END: case_default_ts1755007906254

    // BEGIN: LintSeqNonBlockAssign_ts1755007906252
    always_ff @(posedge clk) begin
        inj_out_g_1755007906252_965 <= inj_b_1755007906248_424;
    end
    // END: LintSeqNonBlockAssign_ts1755007906252

    LintImplicitWidth LintImplicitWidth_inst_1755007906251_9684 (
        .in_wide(inj_data_in_1755007906244_898),
        .out_narrow(inj_out_narrow_1755007906251_356)
    );
    invalid_this_diag_mod invalid_this_diag_mod_inst_1755007906250_2947 (
        .in_val(inj_index_in_1755007906244_141),
        .out_val(inj_out_val_1755007906250_332)
    );
    always_comb begin
        inj_non_ansi_b_1755007906249_321_ts1755007906249 = clk_ts1755007906249;
        inj_non_ansi_basic_output_1755007906249_398_ts1755007906249 = inj_task_in_1755007906243_409_ts1755007906249;
    end
    // END: non_ansi_basic_ts1755007906249

    // BEGIN: mod_comb_logic_ts1755007906248
    always_comb begin
        inj_y_1755007906248_172 = inj_task_in_1755007906243_409 & inj_b_1755007906248_424;
    end
    // END: mod_comb_logic_ts1755007906248

    // BEGIN: mod_default_disable_ts1755007906247
    assign inj_out_1755007906247_294 = inj_enable_in_1755007906247_606;
    // END: mod_default_disable_ts1755007906247

    // BEGIN: super_outside_class_diag_mod_ts1755007906246
    assign inj_out_val_1755007906246_71 = inj_index_in_1755007906244_141;
    // END: super_outside_class_diag_mod_ts1755007906246

    // BEGIN: mod_fixup_target_ts1755007906245
    assign inj_fs_out_target_1755007906245_993 = inj_task_in_1755007906243_409;
    // END: mod_fixup_target_ts1755007906245

    endfunction
    always @(posedge clk) begin
        write_to_var(inj_index_in_1755007906244_141);
    end
    assign inj_driven_var_1755007906245_817 = my_driven_var_ts1755007906245;
    // END: m_driver_check_ts1755007906245

    mod_casez_wildcard mod_casez_wildcard_inst_1755007906244_6961 (
        .in_mask_z(inj_in_mask_z_1755007906244_886),
        .out_match_type_z(inj_out_match_type_z_1755007906244_359)
    );
    mod_split_comb mod_split_comb_inst_1755007906244_4232 (
        .enable(inj_task_in_1755007906243_409),
        .out_a(inj_out_a_1755007906244_149),
        .out_b(inj_out_b_1755007906244_456),
        .data_in(inj_data_in_1755007906244_898)
    );
    ArrayIndexAndPartSelect ArrayIndexAndPartSelect_inst_1755007906244_5035 (
        .data_in(inj_data_in_1755007906244_876),
        .index_in(inj_index_in_1755007906244_141),
        .start_bit(inj_start_bit_1755007906244_488),
        .bit_out(inj_bit_out_1755007906244_911),
        .byte_out(inj_byte_out_1755007906244_368)
    );
    endtask 
    assign inj_task_out_1755007906243_441 = inj_task_in_1755007906243_409;
    // END: task_example_ts1755007906243

    wide_bus_ops wide_bus_ops_inst_1755007906243_1400 (
        .concat_out(inj_concat_out_1755007906243_25),
        .reduce_xor_out(inj_reduce_xor_out_1755007906243_128),
        .wide_sum(inj_wide_sum_1755007906243_508),
        .wide_a(inj_wide_a_1755007906243_97),
        .wide_b(inj_wide_b_1755007906243_535)
    );
endmodule

