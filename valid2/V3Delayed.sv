module shadow_var_mod(
    input  logic       clk,
    input  logic [7:0] din,
    output logic [7:0] dout
);
    logic [7:0] reg_a;
    always @(posedge clk) begin
        reg_a <= din;
    end
    assign dout = reg_a;
endmodule
module shadow_masked_mod(
    input  logic       clk,
    input  logic [7:0] din_vec,
    input  logic       din_bit,
    output logic [7:0] dout
);
    logic [7:0] reg_b;
    always @(posedge clk) begin
        reg_b <= din_vec;
        reg_b[0] = din_bit;
    end
    assign dout = reg_b;
endmodule
module flag_shared_mod(
    input  logic       clk,
    input  logic [7:0] val,
    input  logic [1:0] idx0,
    input  logic [1:0] idx1,
    output logic [7:0] out_val
);
    logic [7:0] arr [0:3][0:3];
    always @(posedge clk) begin
        arr[idx0][idx1] <= val;
    end
    assign out_val = arr[0][0];
endmodule
module value_queue_whole_mod(
    input  logic       clk,
    input  logic [7:0] val,
    output logic [7:0] out0
);
    logic [7:0] arr [0:3];
    integer i;
    always @(posedge clk) begin
        for (i = 0; i < 4; i = i + 1) begin
            arr[i] <= val;
        end
    end
    assign out0 = arr[0];
endmodule
module value_queue_partial_mod(
    input  logic       clk,
    input  logic [7:0] val,
    output logic [7:0] out0
);
    logic [7:0] arr [0:3];
    integer i;
    always @(posedge clk) begin
        for (i = 0; i < 4; i = i + 1) begin
            arr[i][3:0] <= val[3:0];
        end
    end
    assign out0 = arr[0];
endmodule
module flag_unique_mod(
    input  logic       clk,
    input  logic [7:0] val,
    output logic [7:0] out0
);
    logic [7:0] reg_c;
    always @(posedge clk) begin
        fork
            reg_c <= val;
        join
    end
    assign out0 = reg_c;
endmodule
