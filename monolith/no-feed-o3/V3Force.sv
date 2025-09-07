module force_wire (
    input  logic        clk,
    input  logic [7:0]  in_bus,
    output logic [7:0]  out_bus
);
    wire [7:0] sig;
    assign sig = in_bus;
    always @(posedge clk) begin
        if (in_bus[0]) begin
            force sig = ~in_bus;
        end else begin
            release sig;
        end
    end
    assign out_bus = sig;
endmodule
module force_reg_scalar (
    input  logic clk,
    input  logic din,
    output logic dout
);
    logic r;
    always_ff @(posedge clk) begin
        r <= din;
    end
    always_ff @(posedge clk) begin
        if (din) begin
            force r = 1'b0;
        end else begin
            release r;
        end
    end
    assign dout = r;
endmodule
module force_part_select (
    input  logic        clk,
    input  logic [31:0] data_in,
    input  logic        en,
    output logic [31:0] data_out
);
    logic [31:0] store;
    always_ff @(posedge clk) begin
        store <= data_in;
    end
    always_ff @(posedge clk) begin
        if (en) begin
            force store[15:8] = 8'hAA;
        end else begin
            release store[15:8];
        end
    end
    assign data_out = store;
endmodule
module force_real_var (
    input  logic clk,
    input  real  r_in,
    input  logic sel,
    output real  r_out
);
    real r_reg;
    always_ff @(posedge clk) begin
        r_reg <= r_in;
    end
    always_ff @(posedge clk) begin
        if (sel) begin
            force r_reg = 3.14;
        end else begin
            release r_reg;
        end
    end
    assign r_out = r_reg;
endmodule
module force_bit_select (
    input  logic       clk,
    input  logic [3:0] vec_in,
    input  logic       trig,
    output logic [3:0] vec_out
);
    logic [3:0] vec;
    always_ff @(posedge clk) begin
        vec <= vec_in;
    end
    always_ff @(posedge clk) begin
        if (trig) begin
            force vec[2] = 1'b1;
        end else begin
            release vec[2];
        end
    end
    assign vec_out = vec;
endmodule
module force_array_element (
    input  logic       clk,
    input  logic [1:0] idx,
    input  logic       val_in,
    input  logic       mask,
    output logic       out0
);
    logic [7:0] arr [0:3];
    always_ff @(posedge clk) begin
        if (mask) begin
            force arr[idx] = {7'b0, val_in};
        end else begin
            release arr[idx];
        end
    end
    assign out0 = arr[0][0];
endmodule
