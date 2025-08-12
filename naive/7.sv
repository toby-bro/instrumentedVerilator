module struct_ops (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] y
);
    typedef struct packed {
        logic [7:0] sum;
        logic       carry;
    } res_t;
    always_comb begin
        res_t r;
        {r.carry, r.sum} = a + b;
        y = r.sum;
    end
endmodule
module fsm_enum (
    input  logic clk,
    input  logic rst,
    input  logic in_sig,
    output logic state_out
);
    typedef enum logic [1:0] {S0, S1, S2} state_t;
    state_t state;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            state <= S0;
        end else begin
            unique case (state)
                S0: state <= in_sig ? S1 : S0;
                S1: state <= in_sig ? S2 : S0;
                S2: state <= in_sig ? S2 : S0;
                default: state <= S0;
            endcase
        end
    end
    assign state_out = (state == S2);
endmodule
module union_logic (
    input  logic [15:0] data_in,
    output logic [7:0]  hi_byte
);
    union packed {
        logic [15:0] word;
        struct packed {
            logic [7:0] lo;
            logic [7:0] hi;
        } parts;
    } u;
    always_comb begin
        u.word   = data_in;
        hi_byte  = u.parts.hi;
    end
endmodule
module param_mem #(
    parameter WIDTH = 8,
    parameter DEPTH = 4
)(
    input  logic [WIDTH-1:0] din,
    output logic [WIDTH-1:0] dout
);
    logic [WIDTH-1:0] mem [DEPTH-1:0];
    genvar i;
    generate
        for (i = 0; i < DEPTH; i++) begin : g_assign
            always_comb mem[i] = din ^ WIDTH'(i);
        end
    endgenerate
    assign dout = mem[DEPTH-1];
endmodule
module class_adder (
    input  logic [3:0] inA,
    input  logic [3:0] inB,
    output logic [4:0] sum_out
);
    class adder_c;
        function automatic [4:0] add (input logic [3:0] x, input logic [3:0] y);
            return x + y;
        endfunction
    endclass
    always_comb begin
        adder_c a = new();
        sum_out = a.add(inA, inB);
    end
endmodule
module assertions_unit (
    input  logic [7:0] value_in,
    output logic       non_zero
);
    always_comb begin
        non_zero = (value_in != 8'd0);
        assert (value_in !== 8'hxx);
    end
endmodule
