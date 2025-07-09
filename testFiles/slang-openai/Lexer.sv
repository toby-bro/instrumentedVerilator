`define ADD_OP(lhs, rhs) ((lhs) + (rhs))
module arithmetic_ops #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] in1,
    output logic [WIDTH-1:0] out1
);
    assign out1 = in1 + 8'd255 + 32'sd1 - 64'shFF;
endmodule
module bitwise_ops (
    input  logic [3:0] a,
    output logic       y
);
    assign y = a[0] & a[1];
endmodule
module part_select_ops (
    input  logic [31:0] bus,
    output logic [7:0]  slice
);
    assign slice = bus[16 +: 8];
endmodule
module range_minus (
    input  logic [31:0] bus,
    output logic [7:0]  slice_m
);
    assign slice_m = bus[23 -: 8];
endmodule
module string_literals_mod (
    input  logic dummy_in,
    output string out_str
);
    parameter string S = "Hello \"World\"\nSecond Line\tEnd";
    always_comb out_str = S;
endmodule
module real_literals_mod (
    input  logic dummy_in,
    output real  r_out
);
    always_comb r_out = 1.23e-4;
endmodule
module system_id_mod (
    input  logic clk,
    output logic event_detected
);
    logic prev_clk;
    always_ff @(posedge clk) prev_clk <= clk;
    assign event_detected = (clk & ~prev_clk) | $bits(clk);
endmodule
module macro_mod (
    input  logic [7:0] a,
    output logic [7:0] y
);
    assign y = `ADD_OP(a, 8'd1);
endmodule
module concat_mod (
    input  logic [3:0] in4,
    output logic [15:0] out16
);
    assign out16 = {4{in4}};
endmodule
module shift_mod (
    input  logic [31:0] a,
    output logic [31:0] y
);
    assign y = (a <<< 3) ^ (a >>> 2);
endmodule
module strict_eq_mod (
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic       result
);
    assign result = (a === b) || (a !== b);
endmodule
module specify_mod (
    input  wire a,
    input  wire b,
    output wire y
);
    specify
        (a *> y) = (2);
    endspecify
    assign y = a & b;
endmodule
module assign_op_mod (
    input  logic       clk,
    input  logic [7:0] in,
    output logic [7:0] out
);
    always_comb begin
        out = in;
        out /= 2;
        out *= 3;
        out += 1;
        out -= 1;
        out &= 8'hFF;
        out |= 8'h0F;
        out ^= 8'hAA;
    end
endmodule
module assertion_mod (
    input  logic clk,
    input  logic a,
    input  logic b,
    output logic o
);
    property p1; @(posedge clk) a |-> ##1 b; endproperty
    property p2; @(posedge clk) (a && b) |-> ##1 o; endproperty
    assign o = a ^ b;
    assert property (p1);
    assert property (p2);
endmodule
