module M_case_basic(
    input logic [1:0] a,
    output logic [3:0] y
);
    always_comb begin
        case (a)
            2'b00: y = 4'h0;
            2'b01: y = 4'h1;
            2'b10: y = 4'h2;
            default: y = 4'hF;
        endcase
    end
endmodule
module M_case_missing_default(
    input logic [1:0] sel,
    output logic [7:0] outp
);
    always_comb begin
        case (sel)
            2'd0: outp = 8'hAA;
            2'd1: outp = 8'h55;
            2'd2: outp = 8'hFF;
        endcase
    end
endmodule
module M_case_nested(
    input logic [1:0] x,
    input logic [1:0] y,
    output logic [1:0] z
);
    always_comb begin
        case (x)
            2'b00: begin
                case (y)
                    2'b00: z = 2'd0;
                    2'b01: z = 2'd1;
                    default: z = 2'd2;
                endcase
            end
            2'b01: z = 2'd3;
            default: z = 2'd3;
        endcase
    end
endmodule
module M_case_casex(
    input logic [1:0] addr,
    output logic hit
);
    always_comb begin
        casex (addr)
            2'b1x: hit = 1;
            2'b0x: hit = 0;
            default: hit = 0;
        endcase
    end
endmodule
module M_case_casez(
    input logic [2:0] code,
    output logic flag
);
    always_comb begin
        casez (code)
            3'b10?: flag = 1;
            3'b?11: flag = 1;
            default: flag = 0;
        endcase
    end
endmodule
module M_case_unique(
    input logic [1:0] sel,
    output logic [1:0] result
);
    always_comb begin
        unique case (sel)
            2'b00: result = 2'd0;
            2'b01: result = 2'd1;
            2'b10: result = 2'd2;
            default: result = 2'd3;
        endcase
    end
endmodule
module M_case_priority(
    input logic [2:0] val,
    output logic outp
);
    always_comb begin
        priority case (val)
            3'd4: outp = 1;
            3'd2: outp = 1;
            3'd0: outp = 0;
            default: outp = 0;
        endcase
    end
endmodule
module M_case_generate(
    input logic [1:0] sel,
    output logic [3:0] data
);
    parameter logic [1:0] GP = 2'b10;
    generate
        case (GP)
            2'b00: assign data = 4'h1 ^ {4{sel[0]}};
            2'b01: assign data = 4'h2 ^ {4{sel[0]}};
            2'b10: assign data = 4'h4 ^ {4{sel[0]}};
            default: assign data = 4'hF ^ {4{sel[0]}};
        endcase
    endgenerate
endmodule
module M_enum_case(
    input logic [1:0] st,
    output logic [1:0] code
);
    typedef enum logic [1:0] {IDLE=2'b00, BUSY=2'b01, DONE=2'b10, ERROR=2'b11} state_t;
    state_t state;
    always_comb begin
        state = state_t'(st);
        case (state)
            IDLE:    code = 2'd0;
            BUSY:    code = 2'd1;
            DONE:    code = 2'd2;
            default: code = 2'd3;
        endcase
    end
endmodule
module M_inside_op(
    input logic [3:0] val,
    output logic in_set
);
    assign in_set = (val inside {4'd1,4'd3,4'd5,4'd7});
endmodule
