module unary_demo(
    input  logic        clk,
    input  logic signed [7:0] din,
    output logic        out_not
);
    logic signed [7:0] a;
    always_ff @(posedge clk) begin
        a      <= +din;
        a      <= -a;
        a      <= ~a;
        a++;
        --a;
        out_not <= !a;
    end
endmodule
module binary_demo(
    input  logic [15:0] lhs,
    input  logic [15:0] rhs,
    output logic [15:0] arith,
    output logic        comp
);
    assign arith = (lhs + rhs) * (lhs - rhs) / 16'h0004 + (lhs % 5);
    assign comp  = (lhs < rhs) || (lhs == rhs) && (lhs != 0);
endmodule
module conditional_demo(
    input  logic        sel1,
    input  logic        sel2,
    input  logic [7:0]  a,
    input  logic [7:0]  b,
    input  logic [7:0]  c,
    output logic [7:0]  y
);
    assign y = sel1 ? a + b : (sel2 ? a : b);
endmodule
module inside_demo(
    input  logic [7:0] in_val,
    output logic       hit_simple,
    output logic       hit_range
);
    assign hit_simple = (in_val inside {8'd0, 8'd3, 8'd7});
    assign hit_range  = (in_val inside { [8'd10:8'd20] });
endmodule
module concat_demo(
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [31:0] out_vec
);
    assign out_vec = {a, b, {2{a[3:0]}}, 4'b1010};
endmodule
module replication_demo(
    input  logic [3:0] in_bits,
    output logic [15:0] replicated
);
    assign replicated = {4{in_bits}};
endmodule
module streaming_demo(
    input  logic [31:0] in_stream,
    output logic [31:0] out_stream
);
    assign out_stream = { << { in_stream } };
endmodule
module value_range_demo(
    input  logic [7:0] sample,
    output logic       within_tol
);
    logic [7:0] base = 8'd100;
    assign within_tol = (sample inside { [base-8'd5 : base+8'd5] });
endmodule
module precedence_demo(
    input  logic [7:0] flags,
    output logic       result
);
    assign result = flags & 8'h20 != 8'h00;
endmodule
