module fast_case_simplify (
    input  logic [3:0] in_sel,
    output logic [3:0] y
);
    always_comb begin
        unique case (in_sel)
            4'h0: y = 4'h0;
            4'h1: y = 4'h1;
            4'h2: y = 4'h2;
            4'h3: y = 4'h3;
            4'h4: y = 4'h4;
            4'h5: y = 4'h5;
            4'h6: y = 4'h6;
            4'h7: y = 4'h7;
            4'h8: y = 4'h8;
            4'h9: y = 4'h9;
            4'hA: y = 4'hA;
            4'hB: y = 4'hB;
            4'hC: y = 4'hC;
            4'hD: y = 4'hD;
            4'hE: y = 4'hE;
            default: y = 4'hF;
        endcase
    end
endmodule
module casex_overlap (
    input  logic [3:0] sel,
    output logic       match
);
    always_comb begin
        casex (sel)
            4'b1x1x: match = 1'b1;
            4'b1xx1: match = 1'b1;  
            default: match = 1'b0;
        endcase
    end
endmodule
module casez_wildcard (
    input  logic [3:0] sel,
    output logic       flag
);
    always_comb begin
        casez (sel)
            4'b1???: flag = 1'b1;
            4'b0???: flag = 1'b0;
            default : flag = 1'b0;
        endcase
    end
endmodule
module case_inside_range_mod (
    input  logic [3:0] sel,
    output logic       hit
);
    always_comb begin
        unique case inside (sel)
            [4'h0:4'h3]: hit = 1'b1;   
            4'h4, 4'h5 : hit = 1'b0;   
            default    : hit = 1'b0;
        endcase
    end
endmodule
module enum_case_incomplete (
    input  logic [1:0] state_in,
    output logic       odd
);
    typedef enum logic [1:0] {S0 = 2'b00, S1 = 2'b01, S2 = 2'b10, S3 = 2'b11} state_t;
    always_comb begin
        unique0 case (state_t'(state_in))
            S0: odd = 1'b0;
            S1: odd = 1'b1;
            S2: odd = 1'b0;
        endcase
    end
endmodule
module generate_case_module #(
    parameter int MODE = 0
) (
    input  logic in_sig,
    output logic out_sig
);
    generate
        case (MODE)
            0: begin : gen_mode0
                assign out_sig = in_sig;
            end
            1: begin : gen_mode1
                assign out_sig = ~in_sig;
            end
            default: begin : gen_default
                assign out_sig = 1'b0;
            end
        endcase
    endgenerate
endmodule
module priority_case_mod (
    input  logic [3:0] sel,
    output logic [1:0] out
);
    always_comb begin
        priority case (sel)
            4'd0: out = 2'd0;
            4'd1: out = 2'd1;
            4'd2: out = 2'd2;
            default: out = 2'd3;
        endcase
    end
endmodule
module pragma_parallel_case_mod (
    input  logic [2:0] sel,
    output logic       flag
);
    always_comb begin
        (* parallel_case *)
        case (sel)
            3'd0: flag = 1'b0;
            3'd1: flag = 1'b1;
            default: flag = 1'b0;
        endcase
    end
endmodule
