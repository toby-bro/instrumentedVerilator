module comb_logic #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic [WIDTH-1:0] sum
);
    always_comb begin
        sum = (a ^ b) & b;
    end
endmodule
module seq_reg #(parameter N = 4) (
    input  logic clk,
    input  logic reset,
    input  logic [N-1:0] d,
    output logic [N-1:0] q
);
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            q <= '0;
        else
            q <= d;
    end
endmodule
module latch_mod (
    input  logic en,
    input  logic d,
    output logic q
);
    always_latch begin
        if (en)
            q = d;
    end
endmodule
module param_gen #(parameter M = 4) (
    input  logic [M-1:0] din,
    output logic [M-1:0] dout
);
    genvar i;
    generate
        for (i = 0; i < M; i = i + 1) begin
            assign dout[i] = din[i] & ~din[M-1-i];
        end
    endgenerate
endmodule
module seq_fsm (
    input  logic clk,
    input  logic reset,
    input  logic in_sig,
    output logic out_sig
);
    typedef enum logic [1:0] {IDLE=2'b00, S1=2'b01, S2=2'b10} state_t;
    state_t state;
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            state <= IDLE;
        else
            case (state)
                IDLE: state <= in_sig ? S1 : IDLE;
                S1:   state <= in_sig ? S2 : IDLE;
                S2:   state <= IDLE;
                default: state <= IDLE;
            endcase
    end
    assign out_sig = (state == S2);
endmodule
module with_function (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] res
);
    function automatic logic [7:0] mult2(input logic [7:0] x);
        mult2 = x * 2;
    endfunction
    assign res = mult2(a) + b;
endmodule
module with_class (
    input  logic clk,
    input  logic reset,
    input  logic [3:0] d,
    output logic [3:0] q
);
    class regclass;
        logic [3:0] regv;
        function void update(input logic [3:0] in);
            regv = in;
        endfunction
        function logic [3:0] get();
            return regv;
        endfunction
    endclass
    regclass rc;
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            rc = new();
        else
            rc.update(d);
        q <= rc.get();
    end
endmodule
module specify_mod (
    input  wire a,
    input  wire b,
    output wire y
);
    specify
        (a => y) = (1,1);
        (b => y) = (1,1);
    endspecify
    assign y = a & b;
endmodule
module assertion_mod (
    input  logic clk,
    input  logic a,
    input  logic b,
    input  logic c,
    output logic x
);
    assign x = a & b;
    property p1;
        @(posedge clk) b |-> c;
    endproperty
    assert property (p1);
endmodule
module package_mod (
    input  logic [1:0] idx,
    output logic flag
);
    localparam [1:0] VAL0 = 2'b00, VAL1 = 2'b01;
    function logic getflag(input logic [1:0] i);
        case (i)
            VAL0:      getflag = 1'b0;
            VAL1:      getflag = 1'b1;
            default:   getflag = 1'b1;
        endcase
    endfunction
    assign flag = getflag(idx);
endmodule
