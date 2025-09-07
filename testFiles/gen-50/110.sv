module case_selector (
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [1:0] sel_in,
    output logic [3:0] data_out_case
);
    always_comb begin
        case (sel_in)
            2'b00: data_out_case = data0; 
            2'b01: data_out_case = data1; 
            2'b10: data_out_case = data2; 
            default: data_out_case = data3; 
        endcase
    end
endmodule

module mod_basic_bind (
    input logic in1_bind_def,
    output logic out1_bind_def
);
    assign out1_bind_def = ~in1_bind_def;
endmodule

module simple_assign (
    input logic [7:0] in,
    output logic [7:0] out
);
    assign out = in;
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_data0_1755007789442_17,
    input logic [3:0] inj_data1_1755007789442_195,
    input logic [3:0] inj_data2_1755007789442_795,
    input logic [3:0] inj_data3_1755007789442_758,
    input wire inj_g_ctrl_n_1755007789441_292,
    input logic [7:0] inj_in_1755007789441_30,
    input logic [1:0] inj_in_val_1755007789442_364,
    input logic inj_sel_1755007789441_434,
    input logic [2:0] inj_shamt_1755007789442_399,
    input int inj_val_false_1755007789441_184,
    input int inj_val_true_1755007789441_988,
    input wire reset,
    output logic [3:0] inj_data_out_case_1755007789442_83,
    output wire inj_g_out_and_1755007789441_718,
    output wire inj_g_out_or_1755007789441_230,
    output logic [7:0] inj_left_shift_1755007789442_828,
    output logic inj_out1_bind_def_1755007789441_890,
    output logic [7:0] inj_out_1755007789441_433,
    output reg inj_out_res_1755007789442_294,
    output int inj_out_val_1755007789441_220,
    output logic [7:0] inj_right_shift_arith_1755007789442_401,
    output logic [7:0] inj_right_shift_logic_1755007789442_803
);
    // BEGIN: Module_GatePrimitives_ts1755007789441
    // BEGIN: ConditionalOps_ts1755007789441
    // BEGIN: shift_ops_ts1755007789442
    // BEGIN: case_empty_statement_ts1755007789442
    case_selector case_selector_inst_1755007789442_1727 (
        .data3(inj_data3_1755007789442_758),
        .sel_in(inj_in_val_1755007789442_364),
        .data_out_case(inj_data_out_case_1755007789442_83),
        .data0(inj_data0_1755007789442_17),
        .data1(inj_data1_1755007789442_195),
        .data2(inj_data2_1755007789442_795)
    );
    always_comb begin
        inj_out_res_1755007789442_294 = 1'b0;
        case (inj_in_val_1755007789442_364)
            2'b00: inj_out_res_1755007789442_294 = 1'b1;
            2'b01: ;
            2'b10: inj_out_res_1755007789442_294 = 1'b0;
            default: inj_out_res_1755007789442_294 = 1'b1;
        endcase
    end
    // END: case_empty_statement_ts1755007789442

    assign inj_left_shift_1755007789442_828 = inj_in_1755007789441_30 << inj_shamt_1755007789442_399;
    assign inj_right_shift_logic_1755007789442_803 = inj_in_1755007789441_30 >> inj_shamt_1755007789442_399;
    assign inj_right_shift_arith_1755007789442_401 = inj_in_1755007789441_30 >>> inj_shamt_1755007789442_399;
    // END: shift_ops_ts1755007789442

    simple_assign simple_assign_inst_1755007789441_8740 (
        .out(inj_out_1755007789441_433),
        .in(inj_in_1755007789441_30)
    );
    mod_basic_bind mod_basic_bind_inst_1755007789441_6159 (
        .in1_bind_def(inj_sel_1755007789441_434),
        .out1_bind_def(inj_out1_bind_def_1755007789441_890)
    );
    assign inj_out_val_1755007789441_220 = inj_sel_1755007789441_434 ? inj_val_true_1755007789441_988 : inj_val_false_1755007789441_184;
    // END: ConditionalOps_ts1755007789441

    and a1 (inj_g_out_and_1755007789441_718, clk, clk);
    or  o1 (inj_g_out_or_1755007789441_230 , clk, clk);
    // END: Module_GatePrimitives_ts1755007789441
endmodule

