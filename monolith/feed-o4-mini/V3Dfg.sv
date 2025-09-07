module graph_clone_merge #(parameter int WIDTH = 8, parameter int DEPTH = 4) (
    input  logic [WIDTH-1:0] inA,
    input  logic [WIDTH-1:0] inB,
    output logic [WIDTH-1:0] outClone,
    output logic [WIDTH-1:0] outMerge [0:DEPTH-1]
);
    always_comb outClone = inA;
    genvar i;
    generate
        for (i = 0; i < DEPTH; i = i + 1) begin
            assign outMerge[i] = inA | inB;
        end
    endgenerate
endmodule
module unique_name (
    input  logic [7:0]  prefix,
    input  logic [15:0] count,
    output logic [31:0] uniqName
);
    logic [15:0] stub;
    always_comb stub = prefix ^ count;
    assign uniqName = {prefix, stub};
endmodule
module new_var (
    input  logic       isArray,
    input  logic [7:0] val,
    output logic [7:0] out
);
    always_comb begin
        if (isArray) out = {val[3:0], val[7:4]};
        else        out = val;
    end
endmodule
module const_test (
    output logic [7:0] c0,
    output logic [7:0] c1,
    output logic [3:0] c2
);
    localparam [7:0]       P0 = 8'd10;
    localparam signed [7:0]P1 = 8'hFF;
    localparam [3:0]       P2 = 4'b1010;
    assign c0 = P0;
    assign c1 = P1;
    assign c2 = P2;
endmodule
module sel_test (
    input  logic [15:0] in,
    input  logic [3:0]  sel_lsb,
    output logic [3:0]  out
);
    assign out = in[sel_lsb +: 4];
endmodule
module mux_test (
    input  logic [1:0] sel,
    input  logic [7:0] d0, d1, d2, d3,
    output logic [7:0] out
);
    always_comb begin
        case (sel)
            2'd0: out = d0;
            2'd1: out = d1;
            2'd2: out = d2;
            default: out = d3;
        endcase
    end
endmodule
module splice_array_test #(parameter int N = 4, parameter int M = 8, parameter int PW = M * N) (
    input  logic [M-1:0] arr [0:N-1],
    output logic [PW-1:0] outPacked
);
    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin
            assign outPacked[i*M +: M] = arr[i];
        end
    endgenerate
endmodule
module splice_packed_test (
    input  logic [31:0] in,
    output logic [7:0]  out0, out1, out2, out3
);
    assign {out3, out2, out1, out0} = in;
endmodule
module edge_ops (
    input  logic       src_valid,
    input  logic [7:0] src_data,
    input  logic       new_src_valid,
    input  logic [7:0] new_src_data,
    output logic [7:0] data_out
);
    logic [7:0] intermediate;
    always_comb begin
        if      (src_valid)     intermediate = src_data;
        else if (new_src_valid) intermediate = new_src_data;
        else                    intermediate = 8'd0;
    end
    assign data_out = intermediate;
endmodule
module vertex_ops (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic       equal,
    output logic [7:0] hash_out,
    output logic [3:0] popcnt
);
    function logic selfEquals(input logic [7:0] x, input logic [7:0] y);
        selfEquals = (x == y);
    endfunction
    function automatic logic [7:0] selfHash(input logic [7:0] x);
        logic [7:0] h;
        h = 8'd0;
        for (int i = 0; i < 8; i = i + 1)
            h = h ^ {7'd0, x[i]};
        selfHash = h;
    endfunction
    function logic [3:0] countOnes(input logic [7:0] x);
        countOnes = 4'd0;
        for (int i = 0; i < 8; i = i + 1)
            countOnes = countOnes + x[i];
    endfunction
    always_comb begin
        equal    = selfEquals(a, b);
        hash_out = selfHash(a);
        popcnt   = countOnes(a);
    end
endmodule
module var_test (
    input  logic        clk,
    input  logic        en,
    input  logic [7:0]  d,
    output logic [7:0]  q
);
    always_ff @(posedge clk) begin
        if (en) q <= d;
    end
endmodule
module struct_union_test (
    input  logic        ctrl,
    input  logic [7:0]  a,
    input  logic [7:0]  b,
    output logic [15:0] out
);
    typedef struct packed {
        logic [7:0] x;
        logic [7:0] y;
    } mystruct;
    typedef union packed {
        logic [15:0] u;
        mystruct     s;
    } myunion;
    mystruct s1;
    myunion  u1;
    always_comb begin
        s1.x = a;
        s1.y = b;
        u1.s = s1;
        if (ctrl) out = u1.u;
        else      out = {s1.y, s1.x};
    end
endmodule
module typedef_generate_test #(parameter int SIZE = 4) (
    input  logic [SIZE-1:0] in,
    output logic [SIZE-1:0] out
);
    typedef logic [SIZE-1:0] vec_t;
    vec_t r;
    always_comb begin
        for (int i = 0; i < SIZE; i = i + 1)
            r[i] = in[i];
    end
    assign out = r;
endmodule
module queue_test (
    input  logic       clk,
    input  logic       en,
    input  logic [7:0] in,
    output logic [7:0] out
);
    logic [7:0] queue_arr [0:7];
    logic [2:0] head, tail;
    always_ff @(posedge clk) begin
        if (en) begin
            queue_arr[tail] <= in;
            tail <= (tail == 3'd7) ? 3'd0 : tail + 3'd1;
            head <= (head == 3'd7) ? 3'd0 : head + 3'd1;
        end
    end
    assign out = queue_arr[head];
endmodule
module visitor_test (
    input  logic [2:0] op,
    input  logic [7:0] din0, din1, din2, din3,
    output logic [7:0] dout
);
    always_comb begin
        case (op)
            3'd0: dout = din0;
            3'd1: dout = din1;
            3'd2: dout = din2;
            default: dout = din3;
        endcase
    end
endmodule
