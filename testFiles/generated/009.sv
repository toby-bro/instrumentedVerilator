module snippet (
    input wire clk,
    input logic [7:0] inj_in1_1755007753229_561,
    input logic [7:0] inj_in2_1755007753229_972,
    input bit inj_in_bit_1755007753228_724,
    input wire reset,
    output logic [7:0] inj_out1_1755007753229_510,
    output logic [7:0] inj_out2_1755007753229_249,
    output logic inj_out_logic_1755007753228_300,
    output logic [7:0] inj_out_val_1755007753230_964
);
    // BEGIN: DummyHierModule_ts1755007753228
    // BEGIN: dup_expr_ts1755007753230
    logic [7:0] temp_add_ts1755007753229;
    logic [7:0] temp_mult_ts1755007753229;
    logic [7:0] inter1_ts1755007753229;
    logic [7:0] inter2_ts1755007753229;
    logic [7:0] complex_expr_ts1755007753229;
        // BEGIN: used_before_declared_diag_mod_ts1755007753230
        logic [7:0] undeclared_var_ubddm = 8'd5;
        assign inj_out_val_1755007753230_964 = inter1_ts1755007753229 + undeclared_var_ubddm;
        // END: used_before_declared_diag_mod_ts1755007753230

    always_comb begin
        temp_add_ts1755007753229 = inj_in1_1755007753229_561 + inj_in2_1755007753229_972;
        inj_out1_1755007753229_510 = temp_add_ts1755007753229;
        inj_out2_1755007753229_249 = inj_in1_1755007753229_561 + inj_in2_1755007753229_972;
        inter1_ts1755007753229 = inj_in1_1755007753229_561 * 2;
        inter2_ts1755007753229 = inj_in2_1755007753229_972 * 2;
        temp_mult_ts1755007753229 = inter1_ts1755007753229 + inter2_ts1755007753229;
        complex_expr_ts1755007753229 = (inj_in1_1755007753229_561 + inj_in2_1755007753229_972) * (inj_in1_1755007753229_561 - inj_in2_1755007753229_972) + (inj_in1_1755007753229_561 + inj_in2_1755007753229_972);
        if (inj_in1_1755007753229_561 > inj_in2_1755007753229_972) begin
            inj_out1_1755007753229_510 = temp_mult_ts1755007753229;
        end else begin
            inj_out1_1755007753229_510 = temp_add_ts1755007753229;
        end
        if (inj_in2_1755007753229_972 >= inj_in1_1755007753229_561) begin
            inj_out2_1755007753229_249 = temp_add_ts1755007753229;
        end else begin
            inj_out2_1755007753229_249 = temp_mult_ts1755007753229;
        end
        inj_out1_1755007753229_510 = inj_out1_1755007753229_510 + complex_expr_ts1755007753229;
    end
    // END: dup_expr_ts1755007753230

    assign inj_out_logic_1755007753228_300 = inj_in_bit_1755007753228_724;
    // END: DummyHierModule_ts1755007753228
endmodule

