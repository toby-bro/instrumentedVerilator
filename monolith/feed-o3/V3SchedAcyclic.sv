module scalar_cycle (
    input  logic in,
    output logic out
);
    logic a, b;
    always_comb a = b ^ in;
    always_comb b = ~a;
    assign out = a & b;
endmodule
module explicit_sensitivity_loop (
    input  logic in,
    output logic out
);
    logic x, y;
    always @(y or in) x = y |  in;
    always @(x or in) y = x & ~in;
    assign out = x ^ y;
endmodule
module continuous_assign_loop (
    input  logic in,
    output logic out
);
    logic w1, w2;
    assign w1 = ~w2;
    assign w2 =  w1 ^ in;
    assign out = w1;
endmodule
module wide_bus_loop (
    input  logic [7:0] in,
    output logic [7:0] out
);
    logic [127:0] busA;
    logic [127:0] busB;
    always_comb busA = busB + {120'd0, in};
    always_comb busB = busA ^ {16{in}};
    assign out = busA[7:0] | busB[7:0];
endmodule
module array_loop (
    input  logic [3:0] in,
    output logic [3:0] out
);
    logic [3:0] arr [0:3];
    always_comb arr[0] = arr[1] ^ in;
    always_comb arr[1] = arr[2];
    always_comb arr[2] = arr[3];
    always_comb arr[3] = arr[0];
    assign out = arr[0];
endmodule
module struct_loop (
    input  logic [7:0] in,
    output logic [7:0] out
);
    typedef struct packed {
        logic [7:0] hi;
        logic [7:0] lo;
    } word16_t;
    word16_t data1, data2;
    always_comb data1.hi = data2.lo ^ in;
    always_comb data2.lo = data1.hi;
    assign out = data1.hi;
endmodule
module split_candidate_loop (
    input  logic [31:0] in,
    output logic [31:0] out
);
    logic [63:0] big_signal /* verilator split_var */;
    logic [63:0] other_signal;
    always_comb big_signal   = other_signal + {32'd0, in};
    always_comb other_signal = big_signal   ^ {32'hDEADBEEF, in};
    assign out = big_signal[31:0];
endmodule
