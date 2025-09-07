module LintAsyncFovIssue (
    input logic clk,
    input logic in_h,
    input logic rst_n,
    output logic out_i
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            out_i <= 1'b0;
        end else begin
            out_i <= in_h & out_i;
        end
    end
endmodule

module comb_simple (
    input wire clk,
    input bit [7:0] in1,
    input bit [7:0] in2,
    input logic inj_in_h_1755538620270_508,
    input logic [7:0] inj_in_val_t_1755538620271_515,
    input wire rst,
    output logic inj_out_i_1755538620270_495,
    output logic [7:0] inj_out_reg_t_1755538620271_988,
    output bit [7:0] out1,
    output bit [7:0] out2
);
    // BEGIN: split_if_empty_branches_ts1755538620271
    always @(posedge clk) begin
        if (inj_in_h_1755538620270_508) begin
        end else begin
        end
    end
    // END: split_if_empty_branches_ts1755538620271

    LintAsyncFovIssue LintAsyncFovIssue_inst_1755538620270_1927 (
        .in_h(inj_in_h_1755538620270_508),
        .rst_n(rst),
        .out_i(inj_out_i_1755538620270_495),
        .clk(clk)
    );
    always @* begin
        out1 = in1 & in2;
        out2 = in1 | in2;
    end
endmodule

