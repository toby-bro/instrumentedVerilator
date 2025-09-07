module const_wide_assign (
    input  logic clk,
    output logic [127:0] y
);
    always_ff @(posedge clk) begin
        y <= 128'hDEADBEEFCAFEBABE0123456789ABCDEF;
    end
endmodule
module var_wide_assign (
    input  logic clk,
    input  logic [127:0] in_data,
    output logic [127:0] out_data
);
    always_ff @(posedge clk) begin
        out_data <= in_data;
    end
endmodule
module array_sel_assign (
    input  logic       clk,
    input  logic [1:0] idx,
    input  logic [127:0] wr_data,
    output logic [127:0] rd_data
);
    logic [127:0] mem [0:3];
    always_ff @(posedge clk) begin
        mem[idx] <= wr_data;
        rd_data  <= mem[idx];
    end
endmodule
module wide_logic_ops (
    input  logic clk,
    input  logic [127:0] a,
    input  logic [127:0] b,
    output logic [127:0] y_and,
    output logic [127:0] y_or,
    output logic [127:0] y_xor,
    output logic [127:0] y_not
);
    always_ff @(posedge clk) begin
        y_and <= a & b;
        y_or  <= a | b;
        y_xor <= a ^ b;
        y_not <= ~a;
    end
endmodule
module wide_cond_assign (
    input  logic clk,
    input  logic        sel,
    input  logic [127:0] a,
    input  logic [127:0] b,
    output logic [127:0] y
);
    always_ff @(posedge clk) begin
        y <= sel ? a : b;
    end
endmodule
module concat_replicate (
    input  logic clk,
    input  logic [31:0]  in_a,
    input  logic [31:0]  in_b,
    input  logic         bit_sel,
    output logic [63:0]  out_concat,
    output logic [63:0]  out_repl
);
    always_ff @(posedge clk) begin
        out_concat <= {in_a, in_b};
        out_repl   <= {64{bit_sel}};
    end
endmodule
module extend_assign (
    input  logic               clk,
    input  logic signed [7:0]  s8,
    input  logic        [7:0]  u8,
    output logic signed [63:0] s64,
    output logic        [63:0] u64
);
    always_ff @(posedge clk) begin
        s64 <= s8;   
        u64 <= u8;   
    end
endmodule
module partsel_const_rhs (
    input  logic clk,
    input  logic [255:0] in_bus,
    output logic [63:0]  out_part
);
    always_ff @(posedge clk) begin
        out_part <= in_bus[64 +: 64];
    end
endmodule
module partsel_var_rhs (
    input  logic       clk,
    input  logic [255:0] in_bus,
    input  logic  [7:0]  lsb,
    output logic [63:0]  out_part
);
    always_ff @(posedge clk) begin
        out_part <= in_bus[lsb +: 64];
    end
endmodule
module lhs_const_assign (
    input  logic       clk,
    input  logic [15:0] narrow_in,
    output logic [127:0] wide_out
);
    always_ff @(posedge clk) begin
        wide_out[15:0] <= narrow_in;
    end
endmodule
module lhs_var_assign (
    input  logic       clk,
    input  logic [7:0]  narrow_in,
    input  logic [4:0]  pos,
    output logic [63:0] wide_out
);
    always_ff @(posedge clk) begin
        wide_out[pos +: 8] <= narrow_in;
    end
endmodule
module reduce_compare (
    input  logic clk,
    input  logic [255:0] a,
    input  logic [255:0] b,
    output logic eq,
    output logic neq,
    output logic red_or,
    output logic red_and,
    output logic red_xor
);
    always_ff @(posedge clk) begin
        eq       <= (a == b);
        neq      <= (a != b);
        red_or   <= |a;
        red_and  <= &a;
        red_xor  <= ^a;
    end
endmodule
