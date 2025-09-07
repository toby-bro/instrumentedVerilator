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

module ShiftOperations (
    input logic [7:0] data,
    input logic [2:0] shift_val,
    output logic [7:0] left_shift_log,
    output logic [7:0] right_shift_arith,
    output logic [7:0] right_shift_log
);
    assign left_shift_log = data << shift_val;
    assign right_shift_log = data >> shift_val;
    assign right_shift_arith = $signed(data) >>> shift_val;
endmodule

module mod_part_select (
    input wire [31:0] data_in,
    output logic [31:0] data_out
);
    logic [31:0] temp_reg;
    always_comb begin
        temp_reg[7:0] = data_in[7:0];
        temp_reg[15:8] = data_in[23:16];
        temp_reg[31:16] = data_in[15:0];
        temp_reg[0] = data_in[31];
        temp_reg[8] = data_in[0];
        data_out = temp_reg;
    end
endmodule

module split_nested_if (
    input logic clk_m,
    input logic cond1_m,
    input logic cond2_m,
    input logic [7:0] val_a_m,
    input logic [7:0] val_b_m,
    input logic [7:0] val_c_m,
    output logic [7:0] result_m
);
    always @(posedge clk_m) begin
        if (cond1_m) begin
            if (cond2_m) begin
                result_m <= val_a_m;
            end else begin
                result_m <= val_b_m;
            end
        end else begin
            result_m <= val_c_m;
        end
    end
endmodule

module typedef_struct_public_mod (
    input logic [15:0] packed_in,
    output logic [7:0] field2_o
);
    typedef struct packed {
        logic [7:0] field1;
        logic [7:0] field2;
    } my_public_packed_struct_t;
    my_public_packed_struct_t my_struct_var;
    always_comb begin
        my_struct_var = packed_in;
    end
    assign field2_o = my_struct_var.field2;
endmodule

module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007904277_737,
    input logic [7:0] inj_data_1755007904273_831,
    input wire [31:0] inj_data_in_1755007904272_61,
    input wire [3:0] inj_data_in_1755007904274_345,
    input logic [3:0] inj_data_in_1755007904276_66,
    input logic inj_i_1755007904275_652,
    input logic inj_in_d_1755007904276_459,
    input bit inj_in_h_1755007904273_293,
    input logic [15:0] inj_packed_in_1755007904278_979,
    input wire [1:0] inj_sel_1755007904274_510,
    input int inj_sel_in_1755007904276_317,
    input logic [2:0] inj_shift_val_1755007904273_196,
    input logic [7:0] inj_val_b_m_1755007904282_264,
    input logic [7:0] inj_val_c_m_1755007904282_497,
    input logic [9:0] inj_val_in_1755007904275_20,
    input wire reset,
    output reg [3:0] inj_case_out_1755007904274_719,
    output logic [31:0] inj_data_out_1755007904272_837,
    output logic [7:0] inj_data_out_1755007904276_141,
    output logic [7:0] inj_field2_o_1755007904278_523,
    output logic [4:0] inj_internal_out_1755007904277_933,
    output logic [7:0] inj_left_shift_log_1755007904273_989,
    output logic inj_o_1755007904275_650,
    output logic inj_out_1755007904281_598,
    output logic inj_out_e_1755007904276_210,
    output logic inj_out_h_1755007904273_501,
    output logic [7:0] inj_result_m_1755007904282_224,
    output logic [7:0] inj_right_shift_arith_1755007904273_558,
    output logic [7:0] inj_right_shift_log_1755007904273_602,
    output logic [7:0] inj_selected_output_1755007904279_724,
    output logic [9:0] inj_val_out_1755007904275_764
);
    // BEGIN: CoverageHelper_ts1755007904273
    // BEGIN: CaseZExample_ts1755007904274
    wire [3:0] local_data_ts1755007904274;
        // BEGIN: generate_for_block_ts1755007904279
        wire [7:0] data_ts1755007904279 [3:0]; 
            split_nested_if split_nested_if_inst_1755007904282_4458 (
                .result_m(inj_result_m_1755007904282_224),
                .clk_m(clk),
                .cond1_m(inj_in_d_1755007904276_459),
                .cond2_m(inj_i_1755007904275_652),
                .val_a_m(inj_data_1755007904273_831),
                .val_b_m(inj_val_b_m_1755007904282_264),
                .val_c_m(inj_val_c_m_1755007904282_497)
            );
            // BEGIN: simple_and_gate_ts1755007904281
            assign inj_out_1755007904281_598 = inj_in_d_1755007904276_459 & inj_i_1755007904275_652;
            // END: simple_and_gate_ts1755007904281

        genvar i;
        generate
            for (i = 0; i < 4; i = i + 1) begin : data_gen
                assign data_ts1755007904279[i] = 8'(i + 1) * 8'(i + 1);
            end
        endgenerate
        always_comb begin
            case (inj_case_expr_1755007904277_737)
                0: inj_selected_output_1755007904279_724 = data_ts1755007904279[0];
                1: inj_selected_output_1755007904279_724 = data_ts1755007904279[1];
                2: inj_selected_output_1755007904279_724 = data_ts1755007904279[2];
                3: inj_selected_output_1755007904279_724 = data_ts1755007904279[3];
                default: inj_selected_output_1755007904279_724 = 8'hXX;
            endcase
        end
        // END: generate_for_block_ts1755007904279

        typedef_struct_public_mod typedef_struct_public_mod_inst_1755007904278_6160 (
            .packed_in(inj_packed_in_1755007904278_979),
            .field2_o(inj_field2_o_1755007904278_523)
        );
        // BEGIN: case_priority_overlapping_mod_ts1755007904277
        always @* begin
            priority casez (inj_case_expr_1755007904277_737)
                2'b1?: inj_internal_out_1755007904277_933 = 5;
                2'b?1: inj_internal_out_1755007904277_933 = 6;  
                2'b0?: inj_internal_out_1755007904277_933 = 7;
                2'b?0: inj_internal_out_1755007904277_933 = 8;  
                default: inj_internal_out_1755007904277_933 = 9;
            endcase
        end
        // END: case_priority_overlapping_mod_ts1755007904277

        ModuleHierarchy_Low ModuleHierarchy_Low_inst_1755007904276_9615 (
            .data_in(inj_data_in_1755007904276_66),
            .sel_in(inj_sel_in_1755007904276_317),
            .data_out(inj_data_out_1755007904276_141)
        );
        // BEGIN: LintCombBlockAssign_ts1755007904276
        always_comb begin
            inj_out_e_1755007904276_210 = inj_i_1755007904275_652 & inj_in_d_1755007904276_459;
        end
        // END: LintCombBlockAssign_ts1755007904276

        // BEGIN: SimpleAssign_ts1755007904275
        assign inj_val_out_1755007904275_764 = inj_val_in_1755007904275_20;
        // END: SimpleAssign_ts1755007904275

        // BEGIN: child_module_v1_config_dummy_ts1755007904275
        assign inj_o_1755007904275_650 = ~inj_i_1755007904275_652; 
        // END: child_module_v1_config_dummy_ts1755007904275

    assign local_data_ts1755007904274 = inj_data_in_1755007904274_345;
    always @* begin
        casez (inj_sel_1755007904274_510)
            2'b0?: inj_case_out_1755007904274_719 = local_data_ts1755007904274;
            2'b10: inj_case_out_1755007904274_719 = 4'b1111;
            default: inj_case_out_1755007904274_719 = 4'b0000;
        endcase
    end
    // END: CaseZExample_ts1755007904274

    ShiftOperations ShiftOperations_inst_1755007904273_886 (
        .right_shift_log(inj_right_shift_log_1755007904273_602),
        .data(inj_data_1755007904273_831),
        .shift_val(inj_shift_val_1755007904273_196),
        .left_shift_log(inj_left_shift_log_1755007904273_989),
        .right_shift_arith(inj_right_shift_arith_1755007904273_558)
    );
    assign inj_out_h_1755007904273_501 = inj_in_h_1755007904273_293;
    // END: CoverageHelper_ts1755007904273

    mod_part_select mod_part_select_inst_1755007904272_4498 (
        .data_in(inj_data_in_1755007904272_61),
        .data_out(inj_data_out_1755007904272_837)
    );
endmodule

