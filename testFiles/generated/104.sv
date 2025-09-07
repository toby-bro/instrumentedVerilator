interface seq2_if;
    logic [7:0] status_byte;
    modport PortB (output status_byte);
endinterface
interface seq_if;
    logic [31:0] value_a;
    modport PortA (output value_a);
endinterface
module CaseStatementConditions (
    input wire [3:0] data_c,
    input wire [1:0] selector,
    output logic [3:0] out_case_case,
    output logic [3:0] out_case_casex,
    output logic [3:0] out_case_casez
);
    always_comb begin
        case (selector)
            2'b00: out_case_case = data_c;
            2'b01: out_case_case = data_c + 1;
            2'b10: out_case_case = data_c + 2;
            default: out_case_case = 4'bxxxx;
        endcase
        casez (selector)
            2'b0?: out_case_casez = data_c + 10;
            2'b1?: out_case_casez = data_c + 20;
            default: out_case_casez = 4'bzzzz;
        endcase
        casex (selector)
            2'b0?: out_case_casex = data_c - 1;
            2'b1?: out_case_casex = data_c - 2;
            default: out_case_casex = 4'bxxxx;
        endcase
    end
endmodule

module local_not_allowed_diag_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module module_latch (
    input wire [7:0] in_latch_data,
    input wire in_latch_en,
    output reg [7:0] out_latch_reg
);
    always_latch begin
    if (in_latch_en) begin
        out_latch_reg = in_latch_data;
    end
    end
endmodule

module simple_undeclared_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module split_complex_nb (
    input logic clk_s,
    input logic [7:0] i1_s,
    input logic [7:0] i2_s,
    input logic [7:0] i3_s,
    output logic [7:0] o1_s,
    output logic [7:0] o2_s,
    output logic [7:0] o3_s
);
    logic [7:0] t1_s, t2_s;
    always @(posedge clk_s) begin
        t1_s <= i1_s + i2_s;
        o1_s <= t1_s - i3_s;
        t2_s <= i2_s * i3_s;
        o2_s <= t1_s + t2_s;
        o3_s <= t2_s / 2;
    end
endmodule

module snippet (
    input wire clk,
    input wire [3:0] inj_data_c_1755007787332_336,
    input wire [15:0] inj_dcac_start_val_1755007787334_801,
    input logic inj_dummy_in_1755007787330_178,
    input logic [7:0] inj_i2_s_1755007787331_926,
    input logic [7:0] inj_in_b_1755007787330_852,
    input wire [7:0] inj_in_latch_data_1755007787330_688,
    input int inj_in_val_1755007787330_798,
    input logic [31:0] inj_input1_1755007787332_750,
    input wire [1:0] inj_selector_1755007787332_407,
    input logic [7:0] inj_vif_data_1755007787330_336,
    input logic inj_vif_valid_1755007787330_533,
    input wire reset,
    output logic [15:0] inj_dcac_end_val_1755007787334_523,
    output logic inj_dummy_out_1755007787330_342,
    output logic [7:0] inj_o1_s_1755007787331_78,
    output logic [7:0] inj_o2_s_1755007787331_856,
    output logic [7:0] inj_o3_s_1755007787331_774,
    output logic [3:0] inj_out_case_case_1755007787332_858,
    output logic [3:0] inj_out_case_casex_1755007787332_884,
    output logic [3:0] inj_out_case_casez_1755007787332_508,
    output logic [15:0] inj_out_concat_1755007787330_371,
    output logic [7:0] inj_out_data_1755007787330_360,
    output reg [7:0] inj_out_latch_reg_1755007787330_867,
    output int inj_out_val_1755007787330_868,
    output int inj_out_val_1755007787331_466,
    output int inj_out_val_1755007787344_589,
    output logic inj_out_valid_1755007787330_191,
    output logic inj_sequence_valid_1755007787332_553,
    output logic inj_unused_out_1755007787333_338
);
    // BEGIN: virtual_interface_lookup_mod_ts1755007787330
    // BEGIN: ComplexConversions_ts1755007787330
    // BEGIN: module_sequence_different_if_ts1755007787332
    // BEGIN: unreferenced_module_ts1755007787333
    // BEGIN: deep_comb_assign_chain_ts1755007787342
    logic [15:0] t1_ts1755007787335, t2_ts1755007787335, t3_ts1755007787335, t4_ts1755007787335, t5_ts1755007787335, t6_ts1755007787335, t7_ts1755007787335, t8_ts1755007787335, t9_ts1755007787335, t10_ts1755007787335;
    logic [15:0] t11_ts1755007787335, t12_ts1755007787335, t13_ts1755007787335, t14_ts1755007787335, t15_ts1755007787335, t16_ts1755007787335, t17_ts1755007787335, t18_ts1755007787335, t19_ts1755007787335, t20_ts1755007787335;
    logic [15:0] t21_ts1755007787335, t22_ts1755007787335, t23_ts1755007787335, t24_ts1755007787335, t25_ts1755007787335, t26_ts1755007787335, t27_ts1755007787335, t28_ts1755007787335, t29_ts1755007787335, t30_ts1755007787335;
    logic [15:0] t31_ts1755007787335, t32_ts1755007787335, t33_ts1755007787335, t34_ts1755007787335, t35_ts1755007787335, t36_ts1755007787335, t37_ts1755007787335, t38_ts1755007787335, t39_ts1755007787335, t40_ts1755007787335;
        // BEGIN: definition_used_diag_mod_ts1755007787344
        assign inj_out_val_1755007787344_589 = inj_in_val_1755007787330_798;
        // END: definition_used_diag_mod_ts1755007787344

    always_comb begin
        t1_ts1755007787335 = inj_dcac_start_val_1755007787334_801 + 1;
        t2_ts1755007787335 = t1_ts1755007787335 * 2;
        t3_ts1755007787335 = t2_ts1755007787335 - 3;
        t4_ts1755007787335 = t3_ts1755007787335 ^ 4;
        t5_ts1755007787335 = t4_ts1755007787335 | 5;
        t6_ts1755007787335 = t5_ts1755007787335 & 6;
        t7_ts1755007787335 = t6_ts1755007787335 + 7;
        t8_ts1755007787335 = t7_ts1755007787335 - 8;
        t9_ts1755007787335 = t8_ts1755007787335 ^ 9;
        t10_ts1755007787335 = t9_ts1755007787335 | 10;
        t11_ts1755007787335 = t10_ts1755007787335 & 11;
        t12_ts1755007787335 = t11_ts1755007787335 + 12;
        t13_ts1755007787335 = t12_ts1755007787335 - 13;
        t14_ts1755007787335 = t13_ts1755007787335 ^ 14;
        t15_ts1755007787335 = t14_ts1755007787335 | 15;
        t16_ts1755007787335 = t15_ts1755007787335 + 16;
        t17_ts1755007787335 = t16_ts1755007787335 * 17;
        t18_ts1755007787335 = t17_ts1755007787335 - 18;
        t19_ts1755007787335 = t18_ts1755007787335 ^ 19;
        t20_ts1755007787335 = t19_ts1755007787335 | 20;
        t21_ts1755007787335 = t20_ts1755007787335 + 1;
        t22_ts1755007787335 = t21_ts1755007787335 * 2;
        t23_ts1755007787335 = t22_ts1755007787335 - 3;
        t24_ts1755007787335 = t23_ts1755007787335 ^ 4;
        t25_ts1755007787335 = t24_ts1755007787335 | 5;
        t26_ts1755007787335 = t25_ts1755007787335 & 6;
        t27_ts1755007787335 = t26_ts1755007787335 + 7;
        t28_ts1755007787335 = t27_ts1755007787335 - 8;
        t29_ts1755007787335 = t28_ts1755007787335 ^ 9;
        t30_ts1755007787335 = t29_ts1755007787335 | 10;
        t31_ts1755007787335 = t30_ts1755007787335 & 11;
        t32_ts1755007787335 = t31_ts1755007787335 + 12;
        t33_ts1755007787335 = t32_ts1755007787335 - 13;
        t34_ts1755007787335 = t33_ts1755007787335 ^ 14;
        t35_ts1755007787335 = t34_ts1755007787335 | 15;
        t36_ts1755007787335 = t35_ts1755007787335 + 16;
        t37_ts1755007787335 = t36_ts1755007787335 * 17;
        t38_ts1755007787335 = t37_ts1755007787335 - 18;
        t39_ts1755007787335 = t38_ts1755007787335 ^ 19;
        t40_ts1755007787335 = t39_ts1755007787335 | 20;
        inj_dcac_end_val_1755007787334_523 = t40_ts1755007787335;
    end
    // END: deep_comb_assign_chain_ts1755007787342

    assign inj_unused_out_1755007787333_338 = ~inj_dummy_in_1755007787330_178;
    // END: unreferenced_module_ts1755007787333

    CaseStatementConditions CaseStatementConditions_inst_1755007787333_3354 (
        .data_c(inj_data_c_1755007787332_336),
        .selector(inj_selector_1755007787332_407),
        .out_case_case(inj_out_case_case_1755007787332_858),
        .out_case_casez(inj_out_case_casez_1755007787332_508),
        .out_case_casex(inj_out_case_casex_1755007787332_884)
    );
    seq_if sif_port();
    seq2_if sif2_port();
    always_comb begin
        sif_port.value_a = inj_input1_1755007787332_750;
        sif2_port.status_byte = inj_i2_s_1755007787331_926;
        inj_sequence_valid_1755007787332_553 = 1'b1;
    end
    // END: module_sequence_different_if_ts1755007787332

    simple_undeclared_mod simple_undeclared_mod_inst_1755007787331_1597 (
        .in_val(inj_in_val_1755007787330_798),
        .out_val(inj_out_val_1755007787331_466)
    );
    split_complex_nb split_complex_nb_inst_1755007787331_2233 (
        .o1_s(inj_o1_s_1755007787331_78),
        .o2_s(inj_o2_s_1755007787331_856),
        .o3_s(inj_o3_s_1755007787331_774),
        .clk_s(clk),
        .i1_s(inj_in_b_1755007787330_852),
        .i2_s(inj_i2_s_1755007787331_926),
        .i3_s(inj_vif_data_1755007787330_336)
    );
    module_latch module_latch_inst_1755007787330_4209 (
        .in_latch_en(clk),
        .out_latch_reg(inj_out_latch_reg_1755007787330_867),
        .in_latch_data(inj_in_latch_data_1755007787330_688)
    );
    always_comb begin
        inj_out_concat_1755007787330_371 = {inj_vif_data_1755007787330_336, inj_in_b_1755007787330_852};
    end
    // END: ComplexConversions_ts1755007787330

    always_comb begin
        inj_out_data_1755007787330_360  = inj_vif_data_1755007787330_336;
        inj_out_valid_1755007787330_191 = inj_vif_valid_1755007787330_533;
        inj_dummy_out_1755007787330_342 = inj_dummy_in_1755007787330_178;
    end
    // END: virtual_interface_lookup_mod_ts1755007787330

    local_not_allowed_diag_mod local_not_allowed_diag_mod_inst_1755007787330_9613 (
        .out_val(inj_out_val_1755007787330_868),
        .in_val(inj_in_val_1755007787330_798)
    );
endmodule

