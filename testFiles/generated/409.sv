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

module snippet (
    input wire clk,
    input logic inj_in_h_1755007891061_631,
    input wire reset,
    output logic inj_out_i_1755007891061_360
);
    LintAsyncFovIssue LintAsyncFovIssue_inst_1755007891061_6144 (
        .clk(clk),
        .in_h(inj_in_h_1755007891061_631),
        .rst_n(reset),
        .out_i(inj_out_i_1755007891061_360)
    );
endmodule

