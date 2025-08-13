typedef enum logic [1:0] {
    S_IDLE = 2'd0,
    S_RUN  = 2'd1,
    S_STOP = 2'd2
} state_e;
module fast_encoder_mod (
    input  logic [4:0] sel,
    output logic       y
);
    always_comb begin
        unique case (sel)
            5'd0 : y = 1'b0;
            5'd1 : y = 1'b1;
            5'd2 : y = 1'b1;
            5'd3 : y = 1'b0;
            5'd4 : y = 1'b1;
            5'd5 : y = 1'b0;
            5'd6 : y = 1'b1;
            5'd7 : y = 1'b0;
            5'd8 : y = 1'b1;
            default: y = 1'b0;
        endcase
    end
endmodule
module overlap_casez_mod (
    input  logic [2:0] sel,
    output logic       y
);
    always_comb begin
        casez (sel)
            3'b1?? : y = 1'b1;
            3'b?1? : y = 1'b0;
            default: y = 1'b0;
        endcase
    end
endmodule
module casex_example_mod (
    input  logic [2:0] in_sig,
    output logic       y
);
    always_comb begin
        casex (in_sig)
            3'b1x0 : y = 1'b1;
            3'bx1x : y = 1'b0;
            default: y = 1'b0;
        endcase
    end
endmodule
module casez_with_z_mod (
    input  logic [2:0] in_sig,
    output logic       y
);
    always_comb begin
        casez (in_sig)
            3'bz11 : y = 1'b1;
            3'b0z1 : y = 1'b0;
            3'bx0x : y = 1'b1;
            default: y = 1'b0;
        endcase
    end
endmodule
module enum_unique_case_mod (
    input  state_e state,
    output logic   ready
);
    always_comb begin
        unique case (state)
            S_IDLE : ready = 1'b0;
            default: ready = 1'b1;
        endcase
    end
endmodule
module inside_range_case_mod (
    input  logic [3:0] value,
    output logic       flag
);
    always_comb begin
        case (value) inside
            [4:9]   : flag = 1'b1;
            [10:15] : flag = 1'b0;
            default : flag = 1'b0;
        endcase
    end
endmodule
module parallel_case_example_mod (
    input  logic [3:0] sel,
    output logic       y
);
    always_comb begin
        (* parallel_case *) case (sel)
            4'd0 : y = 1'b0;
            4'd1 : y = 1'b1;
            4'd2 : y = 1'b0;
            4'd3 : y = 1'b1;
            default: y = 1'b0;
        endcase
    end
endmodule
module large_case_width_mod (
    input  logic [17:0] in_bus,
    output logic        y
);
    always_comb begin
        case (in_bus)
            18'd0 : y = 1'b0;
            18'd1 : y = 1'b1;
            18'd2 : y = 1'b0;
            18'd3 : y = 1'b1;
            default: y = 1'b0;
        endcase
    end
endmodule
module unique0_case_example_mod (
    input  logic [1:0] a,
    output logic       y
);
    always_comb begin
        unique0 case (a)
            2'd0: y = 1'b0;
            2'd1: y = 1'b1;
        endcase
    end
endmodule
