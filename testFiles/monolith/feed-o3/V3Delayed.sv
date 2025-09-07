module shadow_var_simple (
    input  logic        clk,
    input  logic [7:0]  d,
    output logic [7:0]  q
);
    always_ff @(posedge clk) begin
        q <= d;
    end
endmodule
module shadow_var_masked (
    input  logic        clk,
    input  logic [7:0]  din,
    output logic [7:0]  qout
);
    logic [7:0] r;
    always_ff @(posedge clk) begin
        r[3:0]  <= din[3:0];
        r[7:4]  <= din[7:4];
    end
    assign qout = r;
endmodule
module flag_shared_array (
    input  logic        clk,
    input  logic [7:0]  din,
    input  logic [1:0]  idx_row,
    input  logic [1:0]  idx_col,
    output logic [7:0]  dout
);
    logic [7:0] arr [0:3][0:3];
    always_ff @(posedge clk) begin
        arr[idx_row][idx_col] <= din;
        arr[idx_col][idx_row] <= din;
    end
    assign dout = arr[idx_row][idx_col];
endmodule
module flag_unique_fork (
    input  logic        clk,
    input  logic [7:0]  d,
    output logic [7:0]  q
);
    always_ff @(posedge clk) begin
        fork
            q <= d;
        join
    end
endmodule
module value_queue_whole_loop (
    input  logic        clk,
    input  logic [7:0]  din,
    input  logic [2:0]  sel,
    output logic [7:0]  dout
);
    logic [7:0] arr [0:7];
    always_ff @(posedge clk) begin
        for (int i = 0; i < 8; i++) begin
            arr[i] <= din + i;
        end
    end
    assign dout = arr[sel];
endmodule
module value_queue_partial_loop (
    input  logic         clk,
    input  logic [15:0]  din,
    input  logic [2:0]   sel,
    output logic [15:0]  dout
);
    logic [15:0] arr [0:7];
    always_ff @(posedge clk) begin
        for (int j = 0; j < 8; j++) begin
            arr[j][7:0] <= din[7:0];
        end
    end
    assign dout = arr[sel];
endmodule
module multi_clock_nba (
    input  logic        clk1,
    input  logic        clk2,
    input  logic [7:0]  dina,
    input  logic [7:0]  dinb,
    output logic [7:0]  q
);
    logic [7:0] qa;
    logic [7:0] qb;
    always_ff @(posedge clk1) begin
        qa <= dina;
    end
    always_ff @(posedge clk2) begin
        qb <= dinb;
    end
    assign q = qa ^ qb;
endmodule
