module DummyHierModule (
    input bit in_bit,
    output logic out_logic
);
    assign out_logic = in_bit;
endmodule

module snippet #(
    parameter integer UNUSED_PARAM = 8
) (
    input wire clk,
    input logic [3:0] inj_case_inside_val_1755007875836_392,
    input bit inj_in_bit_1755007875837_241,
    input logic inj_in_m_1755007875836_498,
    input logic [1:0] inj_in_val_1755007875836_567,
    input wire reset,
    output logic [4:0] inj_internal_out_1755007875836_245,
    output logic inj_out_logic_1755007875837_419,
    output logic inj_out_n_1755007875836_229,
    output reg inj_out_res_1755007875836_199
);
    // BEGIN: case_single_default_after_item_ts1755007875836
    // BEGIN: LintParamUnused_ts1755007875836
    // BEGIN: case_parallel_simple_mod_ts1755007875837
    DummyHierModule DummyHierModule_inst_1755007875837_4397 (
        .in_bit(inj_in_bit_1755007875837_241),
        .out_logic(inj_out_logic_1755007875837_419)
    );
    always @* begin
        (* parallel *)
        case (inj_case_inside_val_1755007875836_392)
            4'd0, 4'd1: inj_internal_out_1755007875836_245 = 14;
            4'd2, 4'd3: inj_internal_out_1755007875836_245 = 15;
            default: inj_internal_out_1755007875836_245 = 18;
        endcase
    end
    // END: case_parallel_simple_mod_ts1755007875837

    assign inj_out_n_1755007875836_229 = inj_in_m_1755007875836_498;
    // END: LintParamUnused_ts1755007875836

    always_comb begin
        inj_out_res_1755007875836_199 = 1'b0;
        case (inj_in_val_1755007875836_567)
            2'b01: inj_out_res_1755007875836_199 = 1'b1;
            default: inj_out_res_1755007875836_199 = 1'b0;
            2'b10: inj_out_res_1755007875836_199 = 1'b1;
        endcase
    end
    // END: case_single_default_after_item_ts1755007875836
endmodule

