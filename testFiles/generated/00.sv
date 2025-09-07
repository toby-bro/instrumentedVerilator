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

module mod_split_ff (
    input logic clk,
    input logic [7:0] data_in,
    input logic reset,
    output logic [7:0] out_reg_a,
    output logic [7:0] out_reg_b
);
    logic [7:0]  split_reg_var;
    logic [7:0] other_reg_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_reg_var <= 8'b0;
            other_reg_var <= 8'b0;
            out_reg_a <= 8'b0;
            out_reg_b <= 8'b0;
        end else begin
            split_reg_var <= data_in;
            other_reg_var <= data_in + 2;
            out_reg_a <= split_reg_var;
            out_reg_b <= other_reg_var;
        end
    end
endmodule

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module split_arith_blocking (
    input logic [7:0] op1_u,
    input logic [7:0] op2_u,
    output logic [7:0] diff_u,
    output logic [7:0] prod_u,
    output logic [7:0] sum_u
);
    always @(*) begin
        sum_u = op1_u + op2_u;
        diff_u = op1_u - op2_u;
        prod_u = op1_u * op2_u;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_a_1755004202392_790,
    input logic inj_b_1755004202392_39,
    input logic [7:0] inj_d2_1755004202392_572,
    input logic [7:0] inj_d3_1755004202392_133,
    input logic [7:0] inj_data_in_1755004202392_54,
    input logic [3:0] inj_flags_1755004202392_459,
    input wire reset,
    output logic [7:0] inj_diff_u_1755004202393_771,
    output logic inj_o_bind_status_1755004202392_531,
    output logic [7:0] inj_out1_1755004202392_548,
    output logic [7:0] inj_out_reg_a_1755004202391_523,
    output logic [7:0] inj_out_reg_b_1755004202392_362,
    output logic [7:0] inj_prod_u_1755004202393_200,
    output logic inj_sum_1755004202392_189,
    output logic [7:0] inj_sum_u_1755004202393_557
);
    // BEGIN: module_to_bind_ts1755004202392
    split_arith_blocking split_arith_blocking_inst_1755004202393_5497 (
        .prod_u(inj_prod_u_1755004202393_200),
        .sum_u(inj_sum_u_1755004202393_557),
        .op1_u(inj_data_in_1755004202392_54),
        .op2_u(inj_d2_1755004202392_572),
        .diff_u(inj_diff_u_1755004202393_771)
    );
    always_comb inj_o_bind_status_1755004202392_531 = |inj_flags_1755004202392_459;
    // END: module_to_bind_ts1755004202392

    simple_adder simple_adder_inst_1755004202392_6792 (
        .b(inj_b_1755004202392_39),
        .sum(inj_sum_1755004202392_189),
        .a(inj_a_1755004202392_790)
    );
    dup_logic_ops dup_logic_ops_inst_1755004202392_5165 (
        .d2(inj_d2_1755004202392_572),
        .d3(inj_d3_1755004202392_133),
        .flags(inj_flags_1755004202392_459),
        .out1(inj_out1_1755004202392_548),
        .d1(inj_data_in_1755004202392_54)
    );
    mod_split_ff mod_split_ff_inst_1755004202392_2912 (
        .reset(reset),
        .out_reg_a(inj_out_reg_a_1755004202391_523),
        .out_reg_b(inj_out_reg_b_1755004202392_362),
        .clk(clk),
        .data_in(inj_data_in_1755004202392_54)
    );
endmodule

