module Module_MacroTokens (
    input logic tok_in,
    output logic tok_out
);
    `define PASTE(a,b) a``b
    logic `PASTE(my,_var);
    always_comb begin
        `PASTE(my,_var) = tok_in;
        tok_out         = `PASTE(my,_var);
    end
endmodule

module case_full_parallel_mod (
    input logic [1:0] case_expr,
    output logic [4:0] internal_out
);
    always @* begin
        (* full, parallel *)
        case (case_expr)
            2'b00: internal_out = 1;
            2'b01: internal_out = 2;
            2'b10: internal_out = 3;
            default: internal_out = 4;
        endcase
    end
endmodule

module mod_statement_block_var (
    input logic in_c,
    output logic out_c
);
    always_comb begin : block_with_vars
        int   block_local_int;
        logic [7:0] block_local_logic;
        block_local_int   = in_c ? 10 : 20;
        block_local_logic = block_local_int;
        out_c             = block_local_logic[0];
    end
endmodule

module module_in_program_ref (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
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

module split_input_only_var (
    input logic clk_k,
    input logic control_signal_k,
    input logic [7:0] data_in_k,
    output logic [7:0] data_out_k
);
    always @(posedge clk_k) begin
        if (control_signal_k) begin
            data_out_k <= data_in_k;
        end
    end
endmodule

module timed_assign_unhandled (
    input logic clk,
    input logic [7:0] in,
    output logic [7:0] out
);
    always @(posedge clk) begin
        out <= in;
    end
endmodule

module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007790489_927,
    input logic [3:0] inj_case_inside_val_1755007790480_61,
    input bit [7:0] inj_data1_1755007790479_334,
    input bit [7:0] inj_data2_1755007790479_476,
    input wire [3:0] inj_data_c_1755007790487_236,
    input logic inj_data_ref_in_1755007790479_296,
    input logic [7:0] inj_in_1755007790480_537,
    input logic inj_in_c_1755007790479_334,
    input wire [15:0] inj_in_packed_data_1755007790491_217,
    input int inj_in_val_1755007790484_517,
    input bit inj_sel_1755007790479_881,
    input wire [1:0] inj_selector_1755007790487_259,
    input logic [2:0] inj_shamt_1755007790482_278,
    input wire reset,
    output logic [7:0] inj_data_out_k_1755007790482_616,
    output logic inj_data_ref_out_1755007790479_793,
    output logic [4:0] inj_internal_out_1755007790480_197,
    output logic [4:0] inj_internal_out_1755007790489_349,
    output logic [7:0] inj_left_shift_1755007790482_413,
    output logic inj_o_1755007790479_555,
    output logic inj_o_out_1755007790479_791,
    output logic [7:0] inj_out2_a_1755007790485_654,
    output logic [7:0] inj_out_1755007790480_839,
    output wire [7:0] inj_out_byte_1755007790491_667,
    output logic inj_out_c_1755007790479_65,
    output logic [3:0] inj_out_case_case_1755007790487_999,
    output logic [3:0] inj_out_case_casex_1755007790487_272,
    output logic [3:0] inj_out_case_casez_1755007790487_234,
    output logic [3:0] inj_out_h_1755007790483_244,
    output logic inj_out_its_1755007790481_148,
    output logic inj_out_l_1755007790483_248,
    output logic [3:0] inj_out_l_1755007790483_80,
    output reg inj_out_res_1755007790492_353,
    output int inj_out_val_1755007790484_7,
    output logic inj_q_1755007790480_60,
    output bit [7:0] inj_result1_1755007790479_345,
    output bit [7:0] inj_result2_1755007790479_52,
    output logic [7:0] inj_right_shift_arith_1755007790482_362,
    output logic [7:0] inj_right_shift_logic_1755007790482_565,
    output logic inj_status_out_1755007790479_170,
    output logic inj_tok_out_1755007790481_608,
    inout wire inj_data_inout_1755007790479_296
);
    // BEGIN: another_module_config_dummy_ts1755007790479
    // BEGIN: comb_conditional_ts1755007790479
    // BEGIN: configuration_top_ts1755007790479
    // BEGIN: ansi_directions_ts1755007790480
    logic internal_data = 1'b0;
    // BEGIN: packed_struct_module_ts1755007790491
    typedef struct packed {
        logic [7:0] byte1_ts1755007790491;
        logic [7:0] byte2_ts1755007790491;
    } my_packed_struct_t;
    my_packed_struct_t data_struct;
    // BEGIN: case_default_ts1755007790493
    always_comb begin
        inj_out_res_1755007790492_353 = 1'b0;
        case (inj_case_expr_1755007790489_927)
            2'b01: inj_out_res_1755007790492_353 = 1'b1;
            2'b10: inj_out_res_1755007790492_353 = 1'b0;
            default: inj_out_res_1755007790492_353 = 1'b1;
        endcase
    end
    // END: case_default_ts1755007790493

    assign data_struct = inj_in_packed_data_1755007790491_217;
    assign inj_out_byte_1755007790491_667 = data_struct.byte1_ts1755007790491;
    // END: packed_struct_module_ts1755007790491

    case_full_parallel_mod case_full_parallel_mod_inst_1755007790489_3873 (
        .internal_out(inj_internal_out_1755007790489_349),
        .case_expr(inj_case_expr_1755007790489_927)
    );
    // BEGIN: CaseStatementConditions_ts1755007790487
    always_comb begin
        case (inj_selector_1755007790487_259)
            2'b00: inj_out_case_case_1755007790487_999 = inj_data_c_1755007790487_236;
            2'b01: inj_out_case_case_1755007790487_999 = inj_data_c_1755007790487_236 + 1;
            2'b10: inj_out_case_case_1755007790487_999 = inj_data_c_1755007790487_236 + 2;
            default: inj_out_case_case_1755007790487_999 = 4'bxxxx;
        endcase
        casez (inj_selector_1755007790487_259)
            2'b0?: inj_out_case_casez_1755007790487_234 = inj_data_c_1755007790487_236 + 10;
            2'b1?: inj_out_case_casez_1755007790487_234 = inj_data_c_1755007790487_236 + 20;
            default: inj_out_case_casez_1755007790487_234 = 4'bzzzz;
        endcase
        casex (inj_selector_1755007790487_259)
            2'b0?: inj_out_case_casex_1755007790487_272 = inj_data_c_1755007790487_236 - 1;
            2'b1?: inj_out_case_casex_1755007790487_272 = inj_data_c_1755007790487_236 - 2;
            default: inj_out_case_casex_1755007790487_272 = 4'bxxxx;
        endcase
    end
    // END: CaseStatementConditions_ts1755007790487

    split_basic_nonblocking split_basic_nonblocking_inst_1755007790485_7393 (
        .in2_a(inj_in_1755007790480_537),
        .out2_a(inj_out2_a_1755007790485_654),
        .clk_b(clk)
    );
    module_in_program_ref module_in_program_ref_inst_1755007790484_7676 (
        .in_val(inj_in_val_1755007790484_517),
        .out_val(inj_out_val_1755007790484_7)
    );
    // BEGIN: LintLatch_ts1755007790483
    always_comb begin
        if (inj_data_ref_in_1755007790479_296) begin
            inj_out_l_1755007790483_248 = inj_in_c_1755007790479_334;
        end else begin
            inj_out_l_1755007790483_248 = 1'b0; 
        end
    end
    // END: LintLatch_ts1755007790483

    // BEGIN: concat_assign_ts1755007790483
    assign {inj_out_h_1755007790483_244, inj_out_l_1755007790483_80} = inj_in_1755007790480_537;
    // END: concat_assign_ts1755007790483

    // BEGIN: shift_ops_ts1755007790482
    assign inj_left_shift_1755007790482_413 = inj_in_1755007790480_537 << inj_shamt_1755007790482_278;
    assign inj_right_shift_logic_1755007790482_565 = inj_in_1755007790480_537 >> inj_shamt_1755007790482_278;
    assign inj_right_shift_arith_1755007790482_362 = inj_in_1755007790480_537 >>> inj_shamt_1755007790482_278;
    // END: shift_ops_ts1755007790482

    split_input_only_var split_input_only_var_inst_1755007790482_3922 (
        .data_in_k(inj_in_1755007790480_537),
        .data_out_k(inj_data_out_k_1755007790482_616),
        .clk_k(clk),
        .control_signal_k(inj_in_c_1755007790479_334)
    );
    // BEGIN: ImplicitTimeScaleModule_ts1755007790481
    assign inj_out_its_1755007790481_148 = inj_in_c_1755007790479_334;
    // END: ImplicitTimeScaleModule_ts1755007790481

    Module_MacroTokens Module_MacroTokens_inst_1755007790481_9649 (
        .tok_in(inj_in_c_1755007790479_334),
        .tok_out(inj_tok_out_1755007790481_608)
    );
    // BEGIN: case_parallel_simple_mod_ts1755007790480
    always @* begin
        (* parallel *)
        case (inj_case_inside_val_1755007790480_61)
            4'd0, 4'd1: inj_internal_out_1755007790480_197 = 14;
            4'd2, 4'd3: inj_internal_out_1755007790480_197 = 15;
            default: inj_internal_out_1755007790480_197 = 18;
        endcase
    end
    // END: case_parallel_simple_mod_ts1755007790480

    timed_assign_unhandled timed_assign_unhandled_inst_1755007790480_4913 (
        .in(inj_in_1755007790480_537),
        .out(inj_out_1755007790480_839),
        .clk(clk)
    );
    // BEGIN: basic_d_flipflop_ts1755007790480
    always_ff @(posedge clk) begin
        inj_q_1755007790480_60 <= inj_in_c_1755007790479_334;
    end
    // END: basic_d_flipflop_ts1755007790480

    assign inj_data_inout_1755007790479_296 = internal_data;
    always_comb begin
        inj_data_ref_out_1755007790479_793 = inj_data_ref_in_1755007790479_296;
        internal_data = inj_data_inout_1755007790479_296;
        inj_status_out_1755007790479_170 = internal_data | inj_in_c_1755007790479_334;
    end
    // END: ansi_directions_ts1755007790480

    assign inj_o_out_1755007790479_791 = inj_in_c_1755007790479_334;
    // END: configuration_top_ts1755007790479

    always @* begin
        if (inj_sel_1755007790479_881) begin
            inj_result1_1755007790479_345 = inj_data1_1755007790479_334;
            inj_result2_1755007790479_52 = inj_data1_1755007790479_334;
        end else begin
            inj_result1_1755007790479_345 = inj_data2_1755007790479_476;
            inj_result2_1755007790479_52 = inj_data2_1755007790479_476;
        end
    end
    // END: comb_conditional_ts1755007790479

    assign inj_o_1755007790479_555 = inj_in_c_1755007790479_334 & inj_in_c_1755007790479_334; 
    // END: another_module_config_dummy_ts1755007790479

    mod_statement_block_var mod_statement_block_var_inst_1755007790479_376 (
        .out_c(inj_out_c_1755007790479_65),
        .in_c(inj_in_c_1755007790479_334)
    );
endmodule

