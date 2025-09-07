interface cond_if;
    logic [15:0] control_reg;
    logic [15:0] status_reg;
    modport CtrlStat (output control_reg, input status_reg);
endinterface
module ComplexConversions (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    output logic [15:0] out_concat
);
    always_comb begin
        out_concat = {in_a, in_b};
    end
endmodule

module another_module_config_dummy (
    input logic i,
    output logic o
);
    assign o = i & i; 
endmodule

module procedural_complex (
    input logic [15:0] in1,
    input logic [15:0] in2,
    input logic sel,
    output logic [15:0] out1,
    output logic [15:0] out2
);
    logic [15:0] temp1;
    logic [15:0] temp2;
    always_comb begin
        temp1 = (in1 + in2) * 10;
        if (sel) begin
            temp2 = temp1 ^ (in1 >>> 2);
            out1 = temp2 & in2;
        end else begin
            temp2 = temp1 | (in2 <<< 3);
            out1 = temp2 + in1;
        end
        out2 = temp1 - temp2;
    end
endmodule

module snippet (
    input wire clk,
    input logic [15:0] inj_in1_1755007774977_81,
    input logic [15:0] inj_in2_1755007774977_396,
    input logic [7:0] inj_in_a_1755007774975_704,
    input logic [7:0] inj_in_b_1755007774975_312,
    input logic inj_sel_1755007774977_982,
    input logic [3:0] inj_val_a_1755007774978_80,
    input logic [3:0] inj_val_b_1755007774978_473,
    input wire reset,
    output logic inj_control_status_1755007774980_246,
    output logic [7:0] inj_data_out_1755007774979_163,
    output logic [7:0] inj_diff_u_1755007774976_204,
    output logic inj_o_1755007774980_561,
    output logic [15:0] inj_out1_1755007774977_789,
    output logic [15:0] inj_out2_1755007774977_638,
    output logic [15:0] inj_out_1755007774978_520,
    output logic [15:0] inj_out_concat_1755007774975_931,
    output logic [7:0] inj_prod_u_1755007774976_886,
    output logic [3:0] inj_result_1755007774978_374,
    output logic [7:0] inj_sum_u_1755007774976_623
);
    // BEGIN: split_arith_blocking_ts1755007774977
    // BEGIN: CombinationalLogic_ts1755007774978
    // BEGIN: always_comb_assign_ts1755007774978
    // BEGIN: sequential_register_en_ts1755007774979
    // BEGIN: module_conditional_write_ts1755007774981
    cond_if cif_inst();
    always_comb begin
        if (inj_sel_1755007774977_982) begin
            cif_inst.control_reg = inj_in2_1755007774977_396;
        end else begin
            cif_inst.control_reg = 16'h0;
        end
        inj_control_status_1755007774980_246 = (cif_inst.control_reg != 16'h0);
    end
    // END: module_conditional_write_ts1755007774981

    another_module_config_dummy another_module_config_dummy_inst_1755007774980_7979 (
        .o(inj_o_1755007774980_561),
        .i(inj_sel_1755007774977_982)
    );
    always_ff @(posedge clk) begin
        if (inj_sel_1755007774977_982) begin
            inj_data_out_1755007774979_163 <= inj_in_b_1755007774975_312;
        end
    end
    // END: sequential_register_en_ts1755007774979

    always_comb begin
        inj_out_1755007774978_520 = inj_in1_1755007774977_81;
    end
    // END: always_comb_assign_ts1755007774978

    always_comb begin
        if (inj_sel_1755007774977_982) begin
            inj_result_1755007774978_374 = inj_val_a_1755007774978_80 + inj_val_b_1755007774978_473;
        end else begin
            inj_result_1755007774978_374 = 4'h0;
        end
    end
    // END: CombinationalLogic_ts1755007774978

    procedural_complex procedural_complex_inst_1755007774977_1228 (
        .in2(inj_in2_1755007774977_396),
        .sel(inj_sel_1755007774977_982),
        .out1(inj_out1_1755007774977_789),
        .out2(inj_out2_1755007774977_638),
        .in1(inj_in1_1755007774977_81)
    );
    always @(*) begin
        inj_sum_u_1755007774976_623 = inj_in_a_1755007774975_704 + inj_in_b_1755007774975_312;
        inj_diff_u_1755007774976_204 = inj_in_a_1755007774975_704 - inj_in_b_1755007774975_312;
        inj_prod_u_1755007774976_886 = inj_in_a_1755007774975_704 * inj_in_b_1755007774975_312;
    end
    // END: split_arith_blocking_ts1755007774977

    ComplexConversions ComplexConversions_inst_1755007774975_9478 (
        .out_concat(inj_out_concat_1755007774975_931),
        .in_a(inj_in_a_1755007774975_704),
        .in_b(inj_in_b_1755007774975_312)
    );
endmodule

