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

module reduction_ops (
    input wire clk,
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic inj_a_1755538543665_732,
    input int inj_b_1755538543665_675,
    input wire [31:0] inj_wide_in_1755538543665_941,
    input wire rst,
    output wire [7:0] inj_lower_byte_out_1755538543665_848,
    output logic inj_out_a_1755538543665_512,
    output int inj_out_b_1755538543665_480,
    output wire [7:0] inj_upper_byte_out_1755538543665_25,
    output logic out
);
    // BEGIN: part_select_ops_ts1755538543665
    wire [31:0] processed_wide_ts1755538543665;
    assign processed_wide_ts1755538543665 = inj_wide_in_1755538543665_941 * 2;
    assign inj_upper_byte_out_1755538543665_25 = processed_wide_ts1755538543665[31:24];
    assign inj_lower_byte_out_1755538543665_848 = processed_wide_ts1755538543665[7:0];
    // END: part_select_ops_ts1755538543665

    ModuleBasic ModuleBasic_inst_1755538543665_2641 (
        .a(inj_a_1755538543665_732),
        .b(inj_b_1755538543665_675),
        .out_a(inj_out_a_1755538543665_512),
        .out_b(inj_out_b_1755538543665_480)
    );
    assign out = &in1 | ^in2;
endmodule

