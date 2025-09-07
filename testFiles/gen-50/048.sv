module ContinuousWire (
    input logic din,
    output wire dout
);
    wire internal_w;
    assign internal_w = din;
    assign dout       = internal_w;
endmodule

module PackedStructOps (
    input logic [7:0] byte_val,
    input logic [15:0] packed_in,
    output logic [7:0] byte_out,
    output logic [15:0] packed_out
);
    typedef struct packed {
        logic [7:0] low;
        logic [7:0] high;
    } pair_t;
    pair_t data_pair;
    assign data_pair.high = packed_in[15:8];
    assign data_pair.low = byte_val;
    assign byte_out = data_pair.high;
    assign packed_out[15:8] = data_pair.high;
    assign packed_out[7:0] = data_pair.low + byte_val;
endmodule

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module attributes_on_expr_port (
    input logic i_control,
    input logic i_in,
    output logic o_out
);
    logic internal_sig;
    assign internal_sig = i_in & i_control;
    simple_adder sa_inst(
        .a  (i_in),
        (* fanout_limit = 10 *) .b(i_control),
        .sum(o_out)
    );
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_a_aa_1755007767393_120,
    input logic [7:0] inj_b_aa_1755007767393_709,
    input logic [7:0] inj_c_aa_1755007767393_952,
    input logic inj_i_in_1755007767395_445,
    input logic [2:0] inj_in1_1755007767394_436,
    input logic inj_in2_1755007767394_428,
    input logic [15:0] inj_in2_1755007767396_186,
    input logic [15:0] inj_in3_1755007767396_120,
    input logic [15:0] inj_in4_1755007767396_442,
    input logic [15:0] inj_in5_1755007767396_423,
    input logic [15:0] inj_packed_in_1755007767395_837,
    input wire reset,
    output logic [7:0] inj_byte_out_1755007767395_181,
    output wire inj_dout_1755007767394_132,
    output logic inj_extra_out_1755007767394_664,
    output logic inj_o_out_1755007767395_809,
    output logic inj_out1_1755007767394_667,
    output logic inj_out2_1755007767394_681,
    output logic inj_out_1755007767396_71,
    output logic inj_out_pd_1755007767394_53,
    output logic [15:0] inj_packed_out_1755007767395_659,
    output logic [7:0] inj_x_aa_1755007767393_297,
    output logic [7:0] inj_y_aa_1755007767393_802,
    output logic [7:0] inj_z_aa_1755007767393_137
);
    // BEGIN: split_combo_blocking_ts1755007767394
    // BEGIN: ProgramDefinition_ts1755007767394
    // BEGIN: ansi_implicit_inherit_ts1755007767394
    // BEGIN: arith_comp_ops_ts1755007767396
    assign inj_out_1755007767396_71 = (inj_packed_in_1755007767395_837 + inj_in2_1755007767396_186) * inj_in3_1755007767396_120 > inj_in4_1755007767396_442 - inj_in5_1755007767396_423;
    // END: arith_comp_ops_ts1755007767396

    PackedStructOps PackedStructOps_inst_1755007767395_1978 (
        .byte_val(inj_c_aa_1755007767393_952),
        .packed_in(inj_packed_in_1755007767395_837),
        .byte_out(inj_byte_out_1755007767395_181),
        .packed_out(inj_packed_out_1755007767395_659)
    );
    attributes_on_expr_port attributes_on_expr_port_inst_1755007767395_2005 (
        .o_out(inj_o_out_1755007767395_809),
        .i_control(inj_in2_1755007767394_428),
        .i_in(inj_i_in_1755007767395_445)
    );
    ContinuousWire ContinuousWire_inst_1755007767394_9593 (
        .dout(inj_dout_1755007767394_132),
        .din(inj_in2_1755007767394_428)
    );
    always_comb begin
        inj_out1_1755007767394_667 = |inj_in1_1755007767394_436;
        inj_out2_1755007767394_681 = |inj_in2_1755007767394_428;
        inj_extra_out_1755007767394_664 = inj_out1_1755007767394_667 ^ inj_out2_1755007767394_681;
    end
    // END: ansi_implicit_inherit_ts1755007767394

    assign inj_out_pd_1755007767394_53 = clk;
    // END: ProgramDefinition_ts1755007767394

    always @(*) begin
        inj_x_aa_1755007767393_297 = inj_a_aa_1755007767393_120 + inj_b_aa_1755007767393_709;
        inj_y_aa_1755007767393_802 = inj_x_aa_1755007767393_297 - inj_c_aa_1755007767393_952;
        inj_z_aa_1755007767393_137 = inj_a_aa_1755007767393_120 * inj_c_aa_1755007767393_952;
    end
    // END: split_combo_blocking_ts1755007767394
endmodule

