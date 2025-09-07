module mod_unused_ports (
    input wire unused_in,
    output logic unused_out
);
    assign unused_out = unused_in;
endmodule

module part_select_ops (
    input wire [31:0] wide_in,
    output wire [7:0] lower_byte_out,
    output wire [7:0] upper_byte_out
);
    wire [31:0] processed_wide;
    assign processed_wide = wide_in * 2;
    assign upper_byte_out = processed_wide[31:24];
    assign lower_byte_out = processed_wide[7:0];
endmodule

module split_independent_nb (
    input logic clk_f,
    input logic [7:0] in1_f,
    input logic [7:0] in2_f,
    input logic [7:0] in3_f,
    output logic [7:0] out1_f,
    output logic [7:0] out2_f,
    output logic [7:0] out3_f
);
    always @(posedge clk_f) begin
        out1_f <= in1_f;
        out2_f <= in2_f;
        out3_f <= in3_f;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_i_p1_1755007872002_1,
    input logic inj_i_p2_1755007872002_467,
    input logic [7:0] inj_in1_f_1755007872002_48,
    input logic [7:0] inj_in2_f_1755007872002_430,
    input logic [7:0] inj_in3_f_1755007872002_367,
    input wire [31:0] inj_wide_in_1755007872002_127,
    input wire reset,
    output wire [7:0] inj_lower_byte_out_1755007872002_331,
    output logic inj_o_p_and_1755007872002_234,
    output logic inj_o_p_xor_1755007872002_112,
    output logic [7:0] inj_out1_f_1755007872002_264,
    output logic [7:0] inj_out2_f_1755007872002_501,
    output logic [7:0] inj_out3_f_1755007872002_63,
    output logic inj_unused_out_1755007872002_18,
    output wire [7:0] inj_upper_byte_out_1755007872002_977
);
    // BEGIN: primitive_example_ts1755007872002
    and (inj_o_p_and_1755007872002_234, inj_i_p1_1755007872002_1, inj_i_p2_1755007872002_467);
    xor (inj_o_p_xor_1755007872002_112, inj_i_p1_1755007872002_1, inj_i_p2_1755007872002_467);
    // END: primitive_example_ts1755007872002

    part_select_ops part_select_ops_inst_1755007872002_8633 (
        .wide_in(inj_wide_in_1755007872002_127),
        .lower_byte_out(inj_lower_byte_out_1755007872002_331),
        .upper_byte_out(inj_upper_byte_out_1755007872002_977)
    );
    mod_unused_ports mod_unused_ports_inst_1755007872002_5076 (
        .unused_in(reset),
        .unused_out(inj_unused_out_1755007872002_18)
    );
    split_independent_nb split_independent_nb_inst_1755007872002_188 (
        .out1_f(inj_out1_f_1755007872002_264),
        .out2_f(inj_out2_f_1755007872002_501),
        .out3_f(inj_out3_f_1755007872002_63),
        .clk_f(clk),
        .in1_f(inj_in1_f_1755007872002_48),
        .in2_f(inj_in2_f_1755007872002_430),
        .in3_f(inj_in3_f_1755007872002_367)
    );
endmodule

