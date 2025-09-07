module dup_logic_ops (
    input logic [7:0] d1,
    input logic [7:0] d2,
    input logic [7:0] d3,
    input logic [3:0] flags,
    output logic [7:0] out1
);
    logic cond1, cond2, cond3;
    logic complex_cond1, complex_cond2;
    assign cond1 = flags[0] && flags[1];
    assign cond2 = flags[2] || flags[3];
    assign cond3 = !flags[0];
    assign complex_cond1 = (cond1 || cond2) && cond3;
    assign complex_cond2 = !(flags[0] && flags[1]) || (flags[2] || !flags[3]);
    always_comb begin
        out1 = '0;
        if (complex_cond1) begin
            out1 = d1 + d2;
        end else begin
            out1 = d1 ^ d3;
        end
        if (complex_cond2) begin
            out1 = out1 + d3;
        end else begin
            out1 = out1 - d3;
        end
        if ((flags[0] && flags[1]) && (!flags[2] || flags[3])) begin
            out1 = out1 * 2;
        end
    end
endmodule

module mod_casex_wildcard_overlap_priority (
    input wire clk,
    input bit [3:0] in_mask_x,
    input logic [7:0] inj_d1_1755538372493_782,
    input logic [7:0] inj_d2_1755538372493_992,
    input logic [7:0] inj_d3_1755538372493_331,
    input wire [15:0] inj_dcac_start_val_1755538372484_915,
    input logic [3:0] inj_flags_1755538372493_990,
    input wire rst,
    output logic [15:0] inj_dcac_end_val_1755538372484_956,
    output logic [7:0] inj_out1_1755538372493_456,
    output bit [1:0] out_match_type_x
);
    // BEGIN: deep_comb_assign_chain_ts1755538372492
    logic [15:0] t1_ts1755538372485, t2_ts1755538372485, t3_ts1755538372485, t4_ts1755538372485, t5_ts1755538372485, t6_ts1755538372485, t7_ts1755538372485, t8_ts1755538372485, t9_ts1755538372485, t10_ts1755538372485;
    logic [15:0] t11_ts1755538372485, t12_ts1755538372485, t13_ts1755538372485, t14_ts1755538372485, t15_ts1755538372485, t16_ts1755538372485, t17_ts1755538372485, t18_ts1755538372485, t19_ts1755538372485, t20_ts1755538372485;
    logic [15:0] t21_ts1755538372485, t22_ts1755538372485, t23_ts1755538372485, t24_ts1755538372485, t25_ts1755538372485, t26_ts1755538372485, t27_ts1755538372485, t28_ts1755538372485, t29_ts1755538372485, t30_ts1755538372485;
    logic [15:0] t31_ts1755538372485, t32_ts1755538372485, t33_ts1755538372485, t34_ts1755538372485, t35_ts1755538372485, t36_ts1755538372485, t37_ts1755538372485, t38_ts1755538372485, t39_ts1755538372485, t40_ts1755538372485;
        dup_logic_ops dup_logic_ops_inst_1755538372493_290 (
            .d1(inj_d1_1755538372493_782),
            .d2(inj_d2_1755538372493_992),
            .d3(inj_d3_1755538372493_331),
            .flags(inj_flags_1755538372493_990),
            .out1(inj_out1_1755538372493_456)
        );
    always_comb begin
        t1_ts1755538372485 = inj_dcac_start_val_1755538372484_915 + 1;
        t2_ts1755538372485 = t1_ts1755538372485 * 2;
        t3_ts1755538372485 = t2_ts1755538372485 - 3;
        t4_ts1755538372485 = t3_ts1755538372485 ^ 4;
        t5_ts1755538372485 = t4_ts1755538372485 | 5;
        t6_ts1755538372485 = t5_ts1755538372485 & 6;
        t7_ts1755538372485 = t6_ts1755538372485 + 7;
        t8_ts1755538372485 = t7_ts1755538372485 - 8;
        t9_ts1755538372485 = t8_ts1755538372485 ^ 9;
        t10_ts1755538372485 = t9_ts1755538372485 | 10;
        t11_ts1755538372485 = t10_ts1755538372485 & 11;
        t12_ts1755538372485 = t11_ts1755538372485 + 12;
        t13_ts1755538372485 = t12_ts1755538372485 - 13;
        t14_ts1755538372485 = t13_ts1755538372485 ^ 14;
        t15_ts1755538372485 = t14_ts1755538372485 | 15;
        t16_ts1755538372485 = t15_ts1755538372485 + 16;
        t17_ts1755538372485 = t16_ts1755538372485 * 17;
        t18_ts1755538372485 = t17_ts1755538372485 - 18;
        t19_ts1755538372485 = t18_ts1755538372485 ^ 19;
        t20_ts1755538372485 = t19_ts1755538372485 | 20;
        t21_ts1755538372485 = t20_ts1755538372485 + 1;
        t22_ts1755538372485 = t21_ts1755538372485 * 2;
        t23_ts1755538372485 = t22_ts1755538372485 - 3;
        t24_ts1755538372485 = t23_ts1755538372485 ^ 4;
        t25_ts1755538372485 = t24_ts1755538372485 | 5;
        t26_ts1755538372485 = t25_ts1755538372485 & 6;
        t27_ts1755538372485 = t26_ts1755538372485 + 7;
        t28_ts1755538372485 = t27_ts1755538372485 - 8;
        t29_ts1755538372485 = t28_ts1755538372485 ^ 9;
        t30_ts1755538372485 = t29_ts1755538372485 | 10;
        t31_ts1755538372485 = t30_ts1755538372485 & 11;
        t32_ts1755538372485 = t31_ts1755538372485 + 12;
        t33_ts1755538372485 = t32_ts1755538372485 - 13;
        t34_ts1755538372485 = t33_ts1755538372485 ^ 14;
        t35_ts1755538372485 = t34_ts1755538372485 | 15;
        t36_ts1755538372485 = t35_ts1755538372485 + 16;
        t37_ts1755538372485 = t36_ts1755538372485 * 17;
        t38_ts1755538372485 = t37_ts1755538372485 - 18;
        t39_ts1755538372485 = t38_ts1755538372485 ^ 19;
        t40_ts1755538372485 = t39_ts1755538372485 | 20;
        inj_dcac_end_val_1755538372484_956 = t40_ts1755538372485;
    end
    // END: deep_comb_assign_chain_ts1755538372492

always_comb begin
    out_match_type_x = 2'b01;
    priority casex (in_mask_x)
        4'b1X0Z: begin
            out_match_type_x = 2'b10;
        end
        4'b10?Z: begin
            out_match_type_x = 2'b11;
        end
        4'bZ1?X: begin
            out_match_type_x = 2'b00;
        end
        default: begin
            out_match_type_x = 2'b01;
        end
    endcase
end
endmodule

