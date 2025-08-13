`define COVERTOGGLE(inc, orig, chg) \
    if ((orig) ^ (chg)) begin \
        inc <= inc + 1; \
        chg <= orig; \
    end
module merge_active_mod(
    input  logic        clk,
    input  logic [7:0]  d,
    output logic [7:0]  q
);
    logic [7:0] r;
    always_ff @(posedge clk) begin
        q <= d;
    end
    always_ff @(posedge clk) begin
        r <= d ^ 8'hFF;
    end
endmodule
module cover_toggle_mod(
    input  logic clk,
    input  logic sig,
    output logic [31:0] cov_cnt
);
    logic sampled        = 1'b0;
    logic toggle_change  = 1'b0;
    logic [31:0] cov_cnt_reg = 32'd0;
    assign cov_cnt = cov_cnt_reg;
    always_ff @(posedge clk) begin
        `COVERTOGGLE(cov_cnt_reg, sampled, toggle_change)
        sampled <= sig;
    end
endmodule
module sampled_reg_mod(
    input  logic        clk,
    input  logic [7:0]  data_in,
    output logic [7:0]  data_out
);
    logic [7:0] __Vsampled_data = 8'hA5;
    always_ff @(posedge clk) begin
        __Vsampled_data <= data_in;
        data_out        <= __Vsampled_data;
    end
endmodule
module fork_task_mod(
    input  logic       clk,
    input  logic [3:0] din,
    output logic [3:0] dout
);
    logic [3:0] temp;
    always @(posedge clk) fork
        temp <= din + 4'd1;
        dout <= temp;
    join
endmodule
module multi_edge_mod(
    input  logic clk,
    input  logic rst,
    input  logic d,
    output logic q
);
    logic internal_flag = 1'b0;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) q <= 1'b0;
        else     q <= d;
    end
    always_ff @(negedge clk or posedge rst) begin
        if (rst) internal_flag <= 1'b0;
        else     internal_flag <= ~internal_flag;
    end
endmodule
module multi_sense_or(
    input  logic clk_a,
    input  logic clk_b,
    input  logic data_in,
    output logic data_out
);
    always_ff @(posedge clk_a or posedge clk_b) begin
        data_out <= data_in;
    end
endmodule
