class math_helper;
    function automatic logic [31:0] add (logic [31:0] x, logic [31:0] y);
        add = x + y;
    endfunction
endclass
class rand_c;
    rand bit [7:0] val;
endclass
module gate_array #(parameter WIDTH = 8)
(
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic [WIDTH-1:0] y_and,
    output logic [WIDTH-1:0] y_or
);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : gen_gates
            assign y_and[i] = a[i] & b[i];
            assign y_or[i]  = a[i] | b[i];
        end
    endgenerate
endmodule
module class_compute
(
    input  logic [31:0] in0,
    input  logic [31:0] in1,
    output logic [31:0] result
);
    math_helper mh;
    initial begin
        mh = new();
    end
    always_comb begin
        if (mh != null)
            result = mh.add(in0, in1);
        else
            result = 32'h0;
    end
endmodule
module struct_union_mod
(
    input  logic [15:0] din,
    output logic [7:0]  upper,
    output logic [7:0]  lower
);
    typedef struct packed {
        logic [7:0] byte0;
        logic [7:0] byte1;
    } word16_t;
    typedef union packed {
        word16_t     s;
        logic [15:0] whole;
    } access16_u;
    access16_u u;
    always_comb begin
        u.whole = din;
        upper   = u.s.byte1;
        lower   = u.s.byte0;
    end
endmodule
typedef enum logic [1:0] { S0, S1, S2 } state_e;
module fsm_enum
(
    input  logic clk,
    input  logic rst,
    input  logic in_sig,
    output logic out_sig
);
    state_e state, next;
    always_comb begin
        unique case (state)
            S0:  next = in_sig ? S1 : S0;
            S1:  next = in_sig ? S2 : S0;
            S2:  next = in_sig ? S2 : S1;
            default: next = S0;
        endcase
    end
    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            state <= S0;
        else
            state <= next;
    end
    assign out_sig = (state == S2);
endmodule
module signed_arith #(parameter WIDTH = 16)
(
    input  logic signed [WIDTH-1:0] a,
    input  logic signed [WIDTH-1:0] b,
    output logic signed [WIDTH:0]   sum
);
    localparam int LOG2_WIDTH = $clog2(WIDTH);
    function automatic logic signed [WIDTH:0] add_signed
        (logic signed [WIDTH-1:0] x, logic signed [WIDTH-1:0] y);
        add_signed = x + y;
    endfunction
    always_comb begin
        sum = add_signed(a, b);
    end
endmodule
module rand_gen
(
    input  logic        enable,
    output logic [7:0]  data
);
    rand_c rc;
    initial begin
        rc = new();
        void'(rc.randomize());
    end
    always_comb begin
        data = enable ? rc.val : 8'h00;
    end
endmodule
