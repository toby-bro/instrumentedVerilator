module GenerateFor (
    input logic [3:0] data_in,
    output logic [3:0] data_out
);
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : g_loop
            assign data_out[i] = data_in[i];
        end
    endgenerate
endmodule

module IfElseIfChain (
    input logic [7:0] data0,
    input logic [7:0] data1,
    input logic [7:0] data2,
    input logic [7:0] data3,
    input logic [1:0] sel_code,
    output logic [7:0] selected_data
);
    always_comb begin
        if (sel_code == 2'b00) begin
            selected_data = data0;
        end else if (sel_code == 2'b01) begin
            selected_data = data1;
        end else if (sel_code == 2'b10) begin
            selected_data = data2;
        end else begin
            selected_data = data3;
        end
    end
endmodule

module div_mod_ops (
    input logic [7:0] denominator,
    input logic [15:0] dividend_mod,
    input logic [7:0] divisor_mod,
    input logic [15:0] numerator,
    output logic [15:0] quotient,
    output logic [7:0] remainder
);
    assign quotient = (denominator == 0) ? 16'hFFFF : (numerator / denominator); 
    assign remainder = (divisor_mod == 0) ? 8'hFF : (dividend_mod % divisor_mod);
endmodule

module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007752492_145,
    input logic inj_cond1_m_1755007752492_757,
    input logic inj_cond2_m_1755007752492_438,
    input logic [7:0] inj_data3_1755007752493_490,
    input logic [3:0] inj_data_in_1755007752494_332,
    input logic [7:0] inj_denominator_1755007752492_652,
    input wire [3:0] inj_dffcl_ctrl_mode_1755007752495_137,
    input wire [15:0] inj_dffcl_data_in1_1755007752495_540,
    input wire [15:0] inj_dffcl_data_in2_1755007752495_994,
    input logic [15:0] inj_dividend_mod_1755007752492_672,
    input logic [7:0] inj_divisor_mod_1755007752492_155,
    input logic [31:0] inj_in1_1755007752493_70,
    input logic [31:0] inj_in2_1755007752493_190,
    input bit [2:0] inj_in_state_case_1755007752494_383,
    input int inj_in_val_1755007752502_531,
    input logic [15:0] inj_numerator_1755007752492_828,
    input logic [7:0] inj_val_c_m_1755007752492_466,
    input wire reset,
    output logic [3:0] inj_data_out_1755007752494_670,
    output logic [15:0] inj_data_out_1755007752497_900,
    output logic [15:0] inj_dffcl_data_out_1755007752495_577,
    output logic inj_dummy_out_1755007752499_399,
    output logic [4:0] inj_internal_out_1755007752492_245,
    output logic [31:0] inj_out_1755007752493_420,
    output bit inj_out_priority_case_1755007752494_788,
    output bit inj_out_unique_case_1755007752494_921,
    output int inj_out_val_1755007752502_364,
    output logic [15:0] inj_quotient_1755007752492_776,
    output logic [7:0] inj_remainder_1755007752492_557,
    output logic [7:0] inj_result_m_1755007752492_147,
    output logic [7:0] inj_selected_data_1755007752493_731
);
    // BEGIN: split_nested_if_ts1755007752492
    // BEGIN: case_full_parallel_mod_ts1755007752493
    // BEGIN: always_comb_if_ts1755007752493
    // BEGIN: mod_case_unique_priority_ts1755007752494
    // BEGIN: deep_ff_control_logic_ts1755007752496
    // BEGIN: CombinationalLogicExplicit_ts1755007752497
    // BEGIN: mixed_conn_child_ts1755007752499
    logic dummy_internal_ts1755007752499;
        // BEGIN: local_not_allowed_diag_mod_ts1755007752502
        assign inj_out_val_1755007752502_364 = inj_in_val_1755007752502_531;
        // END: local_not_allowed_diag_mod_ts1755007752502

    always_comb dummy_internal_ts1755007752499 = |inj_denominator_1755007752492_652 | inj_cond2_m_1755007752492_438;
    assign inj_dummy_out_1755007752499_399 = dummy_internal_ts1755007752499;
    // END: mixed_conn_child_ts1755007752499

    always @(inj_cond2_m_1755007752492_438 or inj_dividend_mod_1755007752492_672 or inj_numerator_1755007752492_828) begin
        if (inj_cond2_m_1755007752492_438) begin
            inj_data_out_1755007752497_900 = inj_numerator_1755007752492_828;
        end else begin
            inj_data_out_1755007752497_900 = inj_dividend_mod_1755007752492_672;
        end
    end
    // END: CombinationalLogicExplicit_ts1755007752497

    always_ff @(posedge clk or negedge reset) begin
    if (!reset) begin
        inj_dffcl_data_out_1755007752495_577 <= 16'h0000;
    end else begin
        case (inj_dffcl_ctrl_mode_1755007752495_137)
            4'd0: inj_dffcl_data_out_1755007752495_577 <= inj_dffcl_data_in1_1755007752495_540 + inj_dffcl_data_in2_1755007752495_994;
            4'd1: begin
                if (inj_dffcl_data_in1_1755007752495_540 > inj_dffcl_data_in2_1755007752495_994) begin
                    case (inj_dffcl_ctrl_mode_1755007752495_137[1:0])
                        2'b00: inj_dffcl_data_out_1755007752495_577 <= inj_dffcl_data_in1_1755007752495_540 - inj_dffcl_data_in2_1755007752495_994;
                        2'b01: inj_dffcl_data_out_1755007752495_577 <= inj_dffcl_data_in1_1755007752495_540 & inj_dffcl_data_in2_1755007752495_994;
                        default: inj_dffcl_data_out_1755007752495_577 <= inj_dffcl_data_in1_1755007752495_540 | inj_dffcl_data_in2_1755007752495_994;
                    endcase
                end else begin
                    case (inj_dffcl_ctrl_mode_1755007752495_137[1:0])
                        2'b00: inj_dffcl_data_out_1755007752495_577 <= inj_dffcl_data_in2_1755007752495_994 - inj_dffcl_data_in1_1755007752495_540;
                        2'b01: inj_dffcl_data_out_1755007752495_577 <= inj_dffcl_data_in1_1755007752495_540 ^ inj_dffcl_data_in2_1755007752495_994;
                        default: inj_dffcl_data_out_1755007752495_577 <= ~inj_dffcl_data_in1_1755007752495_540;
                    endcase
                end
            end
            4'd2: begin
                casez (inj_dffcl_data_in1_1755007752495_540[15:13])
                    3'b000: inj_dffcl_data_out_1755007752495_577 <= inj_dffcl_data_in2_1755007752495_994;
                    3'b001: inj_dffcl_data_out_1755007752495_577 <= ~inj_dffcl_data_in2_1755007752495_994;
                    3'b01?: begin
                        if (inj_dffcl_data_in2_1755007752495_994[0]) inj_dffcl_data_out_1755007752495_577 <= inj_dffcl_data_in1_1755007752495_540 << 1;
                        else inj_dffcl_data_out_1755007752495_577 <= inj_dffcl_data_in1_1755007752495_540 >> 1;
                    end
                    3'b1??: begin
                        if (inj_dffcl_ctrl_mode_1755007752495_137[0]) inj_dffcl_data_out_1755007752495_577 <= inj_dffcl_data_in1_1755007752495_540 + 1;
                        else inj_dffcl_data_out_1755007752495_577 <= inj_dffcl_data_in1_1755007752495_540 - 1;
                    end
                    default: inj_dffcl_data_out_1755007752495_577 <= 16'hAAAA;
                endcase
            end
            default: begin
                if (inj_dffcl_ctrl_mode_1755007752495_137[2]) inj_dffcl_data_out_1755007752495_577 <= inj_dffcl_data_in1_1755007752495_540;
                else inj_dffcl_data_out_1755007752495_577 <= inj_dffcl_data_in2_1755007752495_994;
            end
        endcase
    end
    end
    // END: deep_ff_control_logic_ts1755007752496

always_comb begin
    inj_out_unique_case_1755007752494_921 = 1'b0;
    unique case (inj_in_state_case_1755007752494_383)
        3'd0: inj_out_unique_case_1755007752494_921 = 1'b0;
        3'd1: inj_out_unique_case_1755007752494_921 = 1'b1;
        3'd2: inj_out_unique_case_1755007752494_921 = 1'b0;
        3'd1: inj_out_unique_case_1755007752494_921 = 1'b1;
        default: inj_out_unique_case_1755007752494_921 = 1'b1;
    endcase
end
always_comb begin
    inj_out_priority_case_1755007752494_788 = 1'b0;
    priority case (inj_in_state_case_1755007752494_383)
        3'd0: inj_out_priority_case_1755007752494_788 = 1'b0;
        3'd1: inj_out_priority_case_1755007752494_788 = 1'b1;
        3'd2: inj_out_priority_case_1755007752494_788 = 1'b0;
        3'd1: inj_out_priority_case_1755007752494_788 = 1'b1;
        default: inj_out_priority_case_1755007752494_788 = 1'b1;
    endcase
end
    // END: mod_case_unique_priority_ts1755007752494

    GenerateFor GenerateFor_inst_1755007752494_2269 (
        .data_out(inj_data_out_1755007752494_670),
        .data_in(inj_data_in_1755007752494_332)
    );
    IfElseIfChain IfElseIfChain_inst_1755007752493_2203 (
        .sel_code(inj_case_expr_1755007752492_145),
        .selected_data(inj_selected_data_1755007752493_731),
        .data0(inj_divisor_mod_1755007752492_155),
        .data1(inj_val_c_m_1755007752492_466),
        .data2(inj_denominator_1755007752492_652),
        .data3(inj_data3_1755007752493_490)
    );
    always_comb begin
        if (inj_cond1_m_1755007752492_757) begin
            inj_out_1755007752493_420 = inj_in1_1755007752493_70;
        end else begin
            inj_out_1755007752493_420 = inj_in2_1755007752493_190;
        end
    end
    // END: always_comb_if_ts1755007752493

    always @* begin
        (* full, parallel *)
        case (inj_case_expr_1755007752492_145)
            2'b00: inj_internal_out_1755007752492_245 = 1;
            2'b01: inj_internal_out_1755007752492_245 = 2;
            2'b10: inj_internal_out_1755007752492_245 = 3;
            default: inj_internal_out_1755007752492_245 = 4;
        endcase
    end
    // END: case_full_parallel_mod_ts1755007752493

    always @(posedge clk) begin
        if (inj_cond1_m_1755007752492_757) begin
            if (inj_cond2_m_1755007752492_438) begin
                inj_result_m_1755007752492_147 <= inj_denominator_1755007752492_652;
            end else begin
                inj_result_m_1755007752492_147 <= inj_divisor_mod_1755007752492_155;
            end
        end else begin
            inj_result_m_1755007752492_147 <= inj_val_c_m_1755007752492_466;
        end
    end
    // END: split_nested_if_ts1755007752492

    div_mod_ops div_mod_ops_inst_1755007752492_9026 (
        .quotient(inj_quotient_1755007752492_776),
        .remainder(inj_remainder_1755007752492_557),
        .denominator(inj_denominator_1755007752492_652),
        .dividend_mod(inj_dividend_mod_1755007752492_672),
        .divisor_mod(inj_divisor_mod_1755007752492_155),
        .numerator(inj_numerator_1755007752492_828)
    );
endmodule

