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

module mod_if_elseif_chained (
    input bit [7:0] in_value,
    output bit [2:0] out_category
);
always_comb begin
    if (in_value < 10) begin
        out_category = 3'd0;
    end else if (in_value < 50) begin
        out_category = 3'd1;
    end else if (in_value < 100) begin
        out_category = 3'd2;
    end else begin
        out_category = 3'd3;
    end
end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_d1_1755007830085_185,
    input logic [7:0] inj_d2_1755007830085_247,
    input logic [7:0] inj_d3_1755007830085_627,
    input logic [3:0] inj_flags_1755007830085_518,
    input bit [7:0] inj_in_value_1755007830085_822,
    input wire reset,
    output logic [7:0] inj_out1_1755007830085_249,
    output bit [2:0] inj_out_category_1755007830085_87
);
    dup_logic_ops dup_logic_ops_inst_1755007830085_3603 (
        .d3(inj_d3_1755007830085_627),
        .flags(inj_flags_1755007830085_518),
        .out1(inj_out1_1755007830085_249),
        .d1(inj_d1_1755007830085_185),
        .d2(inj_d2_1755007830085_247)
    );
    mod_if_elseif_chained mod_if_elseif_chained_inst_1755007830085_1864 (
        .out_category(inj_out_category_1755007830085_87),
        .in_value(inj_in_value_1755007830085_822)
    );
endmodule

