module partial_write_hazard (
    input  logic        clk,
    input  logic [7:0]  in_low,
    input  logic [7:0]  in_high,
    output logic [15:0] sig_out
);
    logic [15:0] sig;
    always_ff @(posedge clk) begin
        sig[7:0]  <= in_low;
        sig[15:8] <= in_high;
    end
    assign sig_out = sig;
endmodule
module dpi_example (
    input  logic        clk,
    input  logic [31:0] din,
    output logic [31:0] dout
);
    import "DPI-C" function int my_imported (input int a);
    always_ff @(posedge clk) begin
        dout <= my_imported(din);
    end
endmodule
module seq_cycle (
    input  logic        clk,
    input  logic [3:0]  x,
    output logic [3:0]  y
);
    logic [3:0] a;
    logic [3:0] b;
    always_ff @(posedge clk) begin
        a <= b | (x << 1);
        b <= a ^ x;
    end
    assign y = a;
endmodule
module big_logic (
    input  logic clk,
    output logic [7:0] sum
);
    logic [31:0] big_reg [0:199];
    int i;
    always_ff @(posedge clk) begin
        for (i = 0; i < 200; i++) begin
            big_reg[i] <= big_reg[i] + i;
        end
    end
    assign sum = big_reg[0][7:0];
endmodule
module write_read_hazard (
    input  logic clk,
    input  logic data_in,
    input  logic toggle,
    output logic data_out
);
    logic store;
    always_ff @(posedge clk) begin
        if (toggle) begin
            store <= ~store;
        end else begin
            store <= data_in;
        end
        data_out <= store;
    end
endmodule
