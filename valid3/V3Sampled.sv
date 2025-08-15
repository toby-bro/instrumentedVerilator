module sampled_basic (
    input  logic        clk,
    input  logic [3:0]  x,
    output logic [3:0]  y
);
    logic [3:0] y_r;
    assign y = y_r;
    always_ff @(posedge clk) begin
        y_r <= x;
    end
endmodule
module sampled_xor (
    input  logic        clk,
    input  logic [1:0]  a,
    input  logic [1:0]  b,
    output logic [1:0]  c
);
    logic [1:0] c_r;
    assign c = c_r;
    always_ff @(posedge clk) begin
        c_r <= a ^ b;
    end
endmodule
module sampled_flag (
    input  logic clk,
    input  logic flag,
    output logic out_flag
);
    logic flag_d;
    assign out_flag = flag_d;
    always_ff @(posedge clk) begin
        flag_d <= flag;
    end
endmodule
module sampled_accum (
    input  logic        clk,
    input  logic        rst,
    input  logic [7:0]  data,
    output logic [7:0]  sum
);
    logic [7:0] accum;
    assign sum = accum;
    always_ff @(posedge clk) begin
        if (rst) begin
            accum <= 8'd0;
        end else begin
            accum <= accum + data;
        end
    end
endmodule
module sampled_struct (
    input  logic        clk,
    input  logic [3:0]  da,
    input  logic [3:0]  db,
    output logic [3:0]  dout
);
    typedef struct packed {
        logic [3:0] a;
        logic [3:0] b;
    } my_t;
    my_t reg_s;
    assign dout = reg_s.a ^ reg_s.b;
    always_ff @(posedge clk) begin
        reg_s.a <= da;
        reg_s.b <= db;
    end
endmodule
module sampled_enum (
    input  logic        clk,
    input  logic [1:0]  mode,
    output logic        match_out
);
    typedef enum logic [1:0] {
        IDLE  = 2'b00,
        RUN   = 2'b01,
        PAUSE = 2'b10,
        STOP  = 2'b11
    } mode_t;
    mode_t mode_reg;
    assign match_out = (mode_reg == RUN);
    always_ff @(posedge clk) begin
        mode_reg <= mode_t'(mode);
    end
endmodule
