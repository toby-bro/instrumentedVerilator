module sampled_assert_basic(
    input  logic clk,
    input  logic a,
    input  logic b,
    output logic y
);
    property p_ab;
        @(posedge clk) a |-> b;
    endproperty
    assert property (p_ab);
    assign y = a & b;
endmodule
module sampled_seq(
    input  logic clk,
    input  logic x,
    input  logic y_in,
    output logic z
);
    sequence seq1;
        @(posedge clk) x ##1 y_in;
    endsequence
    property prop_seq;
        @(posedge clk) seq1 |-> ##1 x;
    endproperty
    assert property (prop_seq);
    assign z = x ^ y_in;
endmodule
module sampled_struct(
    input  logic       clk,
    input  logic [7:0] s,
    output logic       y
);
    typedef struct packed {
        logic [7:0] f1;
        logic [7:0] f2;
    } my_struct_t;
    my_struct_t sreg;
    always_ff @(posedge clk) begin
        sreg.f1 <= s;
        sreg.f2 <= sreg.f1;
    end
    property p_struct;
        @(posedge clk) sreg.f1 |-> sreg.f2;
    endproperty
    assert property (p_struct);
    assign y = sreg.f2[0];
endmodule
module sampled_enum(
    input  logic       clk,
    input  logic [1:0] din,
    output logic       dout
);
    typedef enum logic [1:0] {
        IDLE = 2'b00,
        RUN  = 2'b01,
        STOP = 2'b10
    } state_t;
    state_t pstate;
    always_ff @(posedge clk) begin
        case (din)
            2'b00: pstate <= IDLE;
            2'b01: pstate <= RUN;
            default: pstate <= STOP;
        endcase
    end
    property p_enum;
        @(posedge clk) (pstate == RUN) |-> (pstate != STOP);
    endproperty
    assert property (p_enum);
    assign dout = pstate[0];
endmodule
module sampled_multi(
    input  logic        clk,
    input  logic [3:0]  a,
    input  logic [3:0]  b,
    input  logic [3:0]  c,
    output logic [3:0]  y
);
    logic [3:0] r;
    always_ff @(posedge clk) begin
        r <= a + b + c;
    end
    property p_multi;
        @(posedge clk) ((a == b) && (b == c)) |-> (r == a + b + c);
    endproperty
    assert property (p_multi);
    assign y = r;
endmodule
