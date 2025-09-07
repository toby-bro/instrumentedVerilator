interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
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
    input logic inj_i_in_1755007832122_32,
    input logic [7:0] inj_in1_f_1755007832121_413,
    input logic [7:0] inj_in2_f_1755007832121_341,
    input logic [7:0] inj_in3_f_1755007832121_166,
    input wire reset,
    output logic inj_o_out_1755007832122_580,
    output logic [7:0] inj_out1_f_1755007832121_953,
    output logic [7:0] inj_out2_f_1755007832121_74,
    output logic [7:0] inj_out3_f_1755007832121_652,
    output logic inj_out_valid_status_1755007832121_885
);
    // BEGIN: module_assign_blocking_ts1755007832122
    // BEGIN: configuration_top_ts1755007832122
    assign inj_o_out_1755007832122_580 = inj_i_in_1755007832122_32;
    // END: configuration_top_ts1755007832122

    my_if vif_inst();
    always_comb begin
        vif_inst.data = inj_in2_f_1755007832121_341;
        vif_inst.valid = 1'b1;
        vif_inst.ready = 1'b0;
        inj_out_valid_status_1755007832121_885 = vif_inst.valid;
    end
    // END: module_assign_blocking_ts1755007832122

    split_independent_nb split_independent_nb_inst_1755007832121_7102 (
        .in1_f(inj_in1_f_1755007832121_413),
        .in2_f(inj_in2_f_1755007832121_341),
        .in3_f(inj_in3_f_1755007832121_166),
        .out1_f(inj_out1_f_1755007832121_953),
        .out2_f(inj_out2_f_1755007832121_74),
        .out3_f(inj_out3_f_1755007832121_652),
        .clk_f(clk)
    );
endmodule

