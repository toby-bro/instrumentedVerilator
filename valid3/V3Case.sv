module priority_case (
    input  logic [3:0] sel,
    output logic [1:0] out
);
    always_comb
        priority case (sel)
            4'b0001: out = 2'd0;
            4'b0010: out = 2'd1;
            4'b0100: out = 2'd2;
            4'b1000: out = 2'd3;
            default: out = 2'd0;
        endcase
endmodule
module casex_overlap (
    input  logic [3:0] a,
    output logic       y
);
    always_comb
        casex (a)
            4'b1x0x: y = 1'b1;
            4'b1xx1: y = 1'b0;
            default: y = 1'b0;
        endcase
endmodule
module casez_example (
    input  logic [2:0] b,
    output logic       z
);
    always_comb
        casez (b)
            3'b1?0: z = 1'b1;
            3'b0?1: z = 1'b0;
            default: z = 1'b0;
        endcase
endmodule
module enum_unique_case (
    input  logic [1:0] state_in,
    output logic       q
);
    typedef enum logic [1:0] {
        S0 = 2'd0,
        S1 = 2'd1,
        S2 = 2'd2,
        S3 = 2'd3
    } state_e;
    state_e state_e_in;
    always_comb begin
        state_e_in = state_e'(state_in);
    end
    always_comb
        unique case (state_e_in)
            S0: q = 1'b0;
            S1: q = 1'b1;
            S2: q = 1'b0;
            S3: q = 1'b1;
        endcase
endmodule
module inside_range_case (
    input  logic [3:0] d,
    output logic [1:0] res
);
    always_comb
        case (d) inside
            [4'b0000:4'b0011]: res = 2'd0;
            [4'b0100:4'b0111]: res = 2'd1;
            default           : res = 2'd2;
        endcase
endmodule
module generate_case #(
    parameter int MODE = 0
) (
    input  logic in1,
    output logic out1
);
    generate
        case (MODE)
            0: begin : g0
                assign out1 = in1;
            end
            1: begin : g1
                assign out1 = ~in1;
            end
            default: begin : gdefault
                assign out1 = 1'b0;
            end
        endcase
    endgenerate
endmodule
