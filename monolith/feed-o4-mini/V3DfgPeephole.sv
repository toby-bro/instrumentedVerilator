module test_extend(input logic [3:0] in, output logic [7:0] zero_ext, output logic signed [7:0] sign_ext);
    assign zero_ext = {4'b0, in};
    assign sign_ext = {{4{in[3]}}, in};
endmodule
module test_unary(input logic [7:0] a, input logic bit_in, output logic [7:0] neg, output logic [7:0] bit_not, output logic log_not);
    assign neg = -$signed(a);
    assign bit_not = ~a;
    assign log_not = !bit_in;
endmodule
module test_reduction(input logic [3:0] a, output logic red_and, output logic red_or, output logic red_xor);
    assign red_and = &a;
    assign red_or = |a;
    assign red_xor = ^a;
endmodule
module test_binary(input logic [7:0] a, input logic [7:0] b, output logic [7:0] sum, output logic [7:0] diff, output logic [7:0] prod, output logic ge, output logic neq);
    assign sum = a + b;
    assign diff = a - b;
    assign prod = a * b;
    assign ge = (a >= b);
    assign neq = (a != b);
endmodule
module test_shift_concat(input logic [3:0] h, input logic [1:0] m, input logic [3:0] l, input logic [1:0] sh, output logic [7:0] concat_out, output logic [7:0] shl_out, output logic [7:0] shr_out);
    assign concat_out = {h, m, l};
    assign shl_out = (concat_out << sh);
    assign shr_out = (concat_out >> sh);
endmodule
module test_part_select(input logic [7:0] data, output logic [3:0] high_nibble, output logic [3:0] low_nibble, output logic mid_bit);
    assign high_nibble = data[7:4];
    assign low_nibble = data[3:0];
    assign mid_bit = data[4];
endmodule
module test_conditional(input logic sel, input logic [7:0] a, input logic [7:0] b, output logic [7:0] cond_out);
    assign cond_out = sel ? (a + 8'd1) : b;
endmodule
module test_replicate_sel(input logic [2:0] in3, input logic [1:0] sel2, output logic [11:0] rep_out, output logic [2:0] sel_out);
    assign rep_out = {4{in3}};
    assign sel_out = rep_out[sel2*3 +: 3];
endmodule
module test_case(input logic [1:0] sel, input logic [7:0] d0, input logic [7:0] d1, input logic [7:0] d2, output logic [7:0] out);
    always_comb begin
        case (sel)
            2'd0: out = d0;
            2'd1: out = d1;
            default: out = d2;
        endcase
    end
endmodule
module test_struct(input logic [3:0] in, output logic [3:0] out);
    typedef struct packed { logic [1:0] hi; logic [1:0] lo; } two2;
    two2 s;
    always_comb begin
        s.hi = in[3:2];
        s.lo = in[1:0];
        out = {s.lo, s.hi};
    end
endmodule
module test_enum(input logic clk, input logic rst, output logic [1:0] state);
    typedef enum logic [1:0] { IDLE = 2'd0, RUN = 2'd1, DONE = 2'd2 } st_t;
    st_t cur, nxt;
    always_comb begin
        case (cur)
            IDLE: nxt = RUN;
            RUN: nxt = DONE;
            default: nxt = IDLE;
        endcase
    end
    always_ff @(posedge clk or posedge rst) begin
        if (rst) cur <= IDLE;
        else cur <= nxt;
    end
    assign state = cur;
endmodule
module test_param_gen(input logic [7:0] in, output logic [7:0] out);
    parameter int N = 4;
    localparam int HALF = N/2;
    wire [7:0] tmp;
    assign tmp = in << HALF;
    generate
        genvar i;
        for (i = 0; i < N; i = i + 1) begin
            assign out[i] = in[i];
        end
    endgenerate
    assign out[7:4] = tmp[7:4];
endmodule
module test_function(input logic [3:0] a, output logic [3:0] b);
    function logic [3:0] swap4(input logic [3:0] x);
        swap4 = {x[1:0], x[3:2]};
    endfunction
    assign b = swap4(a);
endmodule
module test_union(input logic [15:0] in, output logic [7:0] byte0, output logic [7:0] byte1);
    typedef union { logic [15:0] whole; logic [7:0] part [2]; } u16;
    u16 u;
    always_comb begin
        u.whole = in;
    end
    assign byte0 = u.part[0];
    assign byte1 = u.part[1];
endmodule
