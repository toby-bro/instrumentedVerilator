module posedge_reg(
    input  logic        clk,
    input  logic        rst,
    input  logic [7:0]  din,
    output logic [7:0]  q
);
    always_ff @(posedge clk) begin
        if (rst) q <= '0;
        else     q <= din;
    end
endmodule
module negedge_reg(
    input  logic       clk,
    input  logic [3:0] a,
    output logic [3:0] b
);
    always_ff @(negedge clk) begin
        b <= ~a;
    end
endmodule
module multisense_reg(
    input  logic        clk,
    input  logic        en,
    input  logic [7:0]  d0,
    input  logic [7:0]  d1,
    output logic [7:0]  q
);
    always_ff @(posedge clk or posedge en) begin
        if (en) q <= d1;
        else    q <= d0;
    end
endmodule
module wide_toggle(
    input  logic         clk,
    input  logic [63:0]  din,
    output logic         parity
);
    logic [63:0] sampled;
    logic [63:0] diff;
    always_ff @(posedge clk) begin
        sampled <= din;
    end
    assign diff   = sampled ^ din;
    assign parity = ^diff;
endmodule
module task_fork(
    input  logic        clk,
    input  logic [7:0]  din,
    output logic [7:0]  dout
);
    logic [7:0] tmp;
    task automatic inc(input logic [7:0] i, output logic [7:0] o);
        begin
            o = i + 8'd1;
        end
    endtask
    always @(posedge clk) fork
        begin
            inc(din, tmp);
            dout <= tmp;
        end
    join_none
endmodule
module combinational_mux(
    input  logic [7:0] a,
    input  logic [7:0] b,
    input  logic       sel,
    output logic [7:0] y
);
    always_comb begin
        if (sel) y = a;
        else     y = b;
    end
endmodule
module dual_edge_capture(
    input  logic       clk,
    input  logic [3:0] in_data,
    output logic [3:0] out_data
);
    always @(posedge clk or negedge clk) begin
        out_data <= in_data;
    end
endmodule
module complex_if(
    input  logic        clk,
    input  logic [7:0]  din,
    output logic [7:0]  dout
);
    always_ff @(posedge clk) begin
        if (din[7]) begin
            dout <= din;
        end else if (din[6:4] == 3'b101) begin
            dout <= {din[3:0], din[7:4]};
        end else begin
            dout <= ~din;
        end
    end
endmodule
module array_storage(
    input  logic        clk,
    input  logic [1:0]  idx,
    input  logic [7:0]  din,
    output logic [7:0]  dout
);
    logic [7:0] mem [0:3];
    always_ff @(posedge clk) begin
        mem[idx] <= din;
        dout     <= mem[idx];
    end
endmodule
