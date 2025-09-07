module always_multi_stmt_unhandled (
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic [7:0] out1,
    output logic [7:0] out2
);
    always_comb begin
        out1 = in1;
        out2 = in2;
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

module module_in_program_ref (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module module_with_param (
    input logic in,
    output logic named_out
);
    parameter int DELAY = 10;
    logic bind_dummy_in;
    logic bind_dummy_out;
    assign named_out = in;
endmodule

module sequential_logic (
    input logic clk,
    input logic [3:0] data_in,
    input logic rst_n,
    output logic [3:0] data_out
);
    ;
    logic [3:0] internal_reg;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            internal_reg <= 4'h0;
        end else begin
            internal_reg <= data_in;
        end
    end
    assign data_out = internal_reg;
endmodule

module split_combo_nb (
    input logic [7:0] a_bb,
    input logic [7:0] b_bb,
    input logic [7:0] c_bb,
    input logic clk_bb,
    output logic [7:0] x_bb,
    output logic [7:0] y_bb,
    output logic [7:0] z_bb
);
    logic [7:0] temp_bb;
    always @(posedge clk_bb) begin
        x_bb <= a_bb + b_bb;
        y_bb <= x_bb - c_bb;
        z_bb <= a_bb * c_bb;
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_a_bb_1755007827649_281,
    input logic [7:0] inj_b_bb_1755007827649_843,
    input logic [7:0] inj_c_bb_1755007827649_348,
    input logic [31:0] inj_data_in_1755007827646_245,
    input bit inj_dummy_in_1755007827647_168,
    input logic [3:0] inj_i_bind_control_1755007827646_463,
    input int inj_index_in_1755007827646_788,
    input logic [4:0] inj_start_bit_1755007827646_383,
    input logic inj_tok_in_1755007827647_747,
    input wire reset,
    output logic inj_bit_out_1755007827646_747,
    output logic [7:0] inj_byte_out_1755007827646_810,
    output logic [3:0] inj_data_out_1755007827648_892,
    output bit inj_dummy_out_1755007827647_843,
    output wire inj_match_x_neq_1755007827654_761,
    output wire inj_match_z_eq_1755007827654_905,
    output logic inj_named_out_1755007827651_956,
    output logic inj_o_bind_status_1755007827646_253,
    output logic [7:0] inj_out1_1755007827652_999,
    output logic [7:0] inj_out2_1755007827652_183,
    output logic [7:0] inj_out_1755007827649_316,
    output logic inj_out_bit_1755007827650_548,
    output logic [7:0] inj_out_reg_h_1755007827652_637,
    output logic [3:0] inj_out_slice_1755007827650_559,
    output int inj_out_val_1755007827647_848,
    output logic inj_tok_out_1755007827647_215,
    output logic [7:0] inj_x_bb_1755007827649_741,
    output logic [7:0] inj_y_bb_1755007827649_217,
    output logic [7:0] inj_z_bb_1755007827649_748,
    inout wire [3:0] inj_data_io_1755007827654_116
);
    // BEGIN: module_to_bind_ts1755007827646
    // BEGIN: ArrayIndexAndPartSelect_ts1755007827646
    logic [31:0] internal_data = inj_data_in_1755007827646_245;
    // BEGIN: module_finish_numbers_ts1755007827647
    parameter p_finish_0 = 0;
    parameter p_finish_1 = 1;
    parameter p_finish_2 = 2;
    parameter p_finish_other_3 = 3;
    parameter p_finish_large_100 = 100;
    parameter p_finish_neg_minus1 = -1;
    localparam lp_finish_0 = 0;
    localparam lp_finish_1 = 1;
    localparam lp_finish_2 = 2;
    localparam lp_finish_other_5 = 5;
    localparam lp_finish_neg_minus10 = -10;
    // BEGIN: CaseEq_ts1755007827654
    assign inj_match_z_eq_1755007827654_905 = (inj_data_io_1755007827654_116 === 4'b101z);
    assign inj_match_x_neq_1755007827654_761 = (inj_data_io_1755007827654_116 !== 4'b1x0x);
    // END: CaseEq_ts1755007827654

    // BEGIN: split_if_only_then_ts1755007827653
    always @(posedge clk) begin
        if (inj_tok_in_1755007827647_747) begin
            inj_out_reg_h_1755007827652_637 <= inj_c_bb_1755007827649_348;
        end
    end
    // END: split_if_only_then_ts1755007827653

    always_multi_stmt_unhandled always_multi_stmt_unhandled_inst_1755007827652_4504 (
        .out1(inj_out1_1755007827652_999),
        .out2(inj_out2_1755007827652_183),
        .in1(inj_c_bb_1755007827649_348),
        .in2(inj_b_bb_1755007827649_843)
    );
    module_with_param module_with_param_inst_1755007827651_2965 (
        .in(inj_tok_in_1755007827647_747),
        .named_out(inj_named_out_1755007827651_956)
    );
    element_select_packed element_select_packed_inst_1755007827650_5670 (
        .in_vec(inj_c_bb_1755007827649_348),
        .index_in(inj_index_in_1755007827646_788),
        .out_bit(inj_out_bit_1755007827650_548),
        .out_slice(inj_out_slice_1755007827650_559)
    );
    // BEGIN: sub_inst_array_mod_ts1755007827649
    assign inj_out_1755007827649_316 = inj_c_bb_1755007827649_348;
    // END: sub_inst_array_mod_ts1755007827649

    split_combo_nb split_combo_nb_inst_1755007827649_8196 (
        .clk_bb(clk),
        .x_bb(inj_x_bb_1755007827649_741),
        .y_bb(inj_y_bb_1755007827649_217),
        .z_bb(inj_z_bb_1755007827649_748),
        .a_bb(inj_a_bb_1755007827649_281),
        .b_bb(inj_b_bb_1755007827649_843),
        .c_bb(inj_c_bb_1755007827649_348)
    );
    sequential_logic sequential_logic_inst_1755007827648_6215 (
        .data_out(inj_data_out_1755007827648_892),
        .clk(clk),
        .data_in(inj_i_bind_control_1755007827646_463),
        .rst_n(reset)
    );
    // BEGIN: Module_MacroTokens_ts1755007827648
    `define PASTE(a,b) a``b
    logic `PASTE(my,_var);
    always_comb begin
        `PASTE(my,_var) = inj_tok_in_1755007827647_747;
        inj_tok_out_1755007827647_215         = `PASTE(my,_var);
    end
    // END: Module_MacroTokens_ts1755007827648

    module_in_program_ref module_in_program_ref_inst_1755007827647_9093 (
        .in_val(inj_index_in_1755007827646_788),
        .out_val(inj_out_val_1755007827647_848)
    );
    assign inj_dummy_out_1755007827647_843 = inj_dummy_in_1755007827647_168;
    // END: module_finish_numbers_ts1755007827647

    assign inj_bit_out_1755007827646_747 = internal_data[inj_index_in_1755007827646_788];
    assign inj_byte_out_1755007827646_810 = internal_data[inj_start_bit_1755007827646_383 +: 8];
    // END: ArrayIndexAndPartSelect_ts1755007827646

    always_comb inj_o_bind_status_1755007827646_253 = |inj_i_bind_control_1755007827646_463;
    // END: module_to_bind_ts1755007827646
endmodule

