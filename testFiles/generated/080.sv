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

module snippet (
    input wire clk,
    input logic inj_a_1755007778767_479,
    input int inj_b_1755007778767_594,
    input logic [7:0] inj_in1_1755007778767_957,
    input logic [7:0] inj_in2_1755007778767_272,
    input wire reset,
    output logic [7:0] inj_out1_1755007778767_781,
    output logic [7:0] inj_out2_1755007778767_106,
    output logic inj_out_a_1755007778767_580,
    output int inj_out_b_1755007778767_238
);
    // BEGIN: always_multi_stmt_unhandled_ts1755007778767
    ModuleBasic ModuleBasic_inst_1755007778767_2202 (
        .a(inj_a_1755007778767_479),
        .b(inj_b_1755007778767_594),
        .out_a(inj_out_a_1755007778767_580),
        .out_b(inj_out_b_1755007778767_238)
    );
    always_comb begin
        inj_out1_1755007778767_781 = inj_in1_1755007778767_957;
        inj_out2_1755007778767_106 = inj_in2_1755007778767_272;
    end
    // END: always_multi_stmt_unhandled_ts1755007778767
endmodule

