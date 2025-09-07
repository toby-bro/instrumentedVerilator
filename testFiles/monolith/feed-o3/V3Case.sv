module fast_case_encoder (input  logic [3:0] sel,
                          output logic [7:0] out);
    always_comb begin
        case (sel)
            4'd0 : out = 8'h01;
            4'd1 : out = 8'h02;
            4'd2 : out = 8'h04;
            4'd3 : out = 8'h08;
            4'd4 : out = 8'h10;
            4'd5 : out = 8'h20;
            4'd6 : out = 8'h40;
            4'd7 : out = 8'h80;
            4'd8 : out = 8'hFF;
            default: out = 8'h00;
        endcase
    end
endmodule
module overlap_casez (input  logic [3:0] in,
                      output logic       y);
    always_comb begin
        casez (in)
            4'b1???: y = 1'b1;
            4'b1?1?: y = 1'b0;
            default : y = 1'b0;
        endcase
    end
endmodule
module casex_suggestion (input  logic [3:0] in,
                         output logic       y);
    always_comb begin
        casex (in)
            4'b1???: y = 1'b1;
            default : y = 1'b0;
        endcase
    end
endmodule
module casez_x_constant (input  logic [1:0] in,
                         output logic       y);
    always_comb begin
        casez (in)
            2'b1x : y = 1'b1;   
            default: y = 1'b0;
        endcase
    end
endmodule
module case_inside_range (input  logic [3:0] in,
                          output logic [1:0] out);
    always_comb begin
        case (in) inside
            [4'd0 : 4'd3] : out = 2'd0;
            [4'd4 : 4'd7] : out = 2'd1;
            default       : out = 2'd2;
        endcase
    end
endmodule
module priority_case_example (input  logic [2:0] in,
                              output logic       y);
    always_comb begin
        priority case (in)
            3'b000 : y = 1'b0;
            3'b0?1 : y = 1'b1; 
            default: y = 1'b0;
        endcase
    end
endmodule
module enum_unique0_incomplete (input  logic [1:0] in,
                                output logic       out);
    typedef enum logic [1:0] {IDLE = 2'd0, RUN = 2'd1, STOP = 2'd2} state_t;
    state_t state;
    always_comb begin
        state = state_t'(in);   
        out   = 1'b0;           
        unique0 case (state)
            IDLE: out = 1'b0;
            RUN : out = 1'b1;
        endcase
    end
endmodule
module generate_case_module #(parameter MODE = 0)
                             (input  logic a,
                              output logic y);
    generate
        case (MODE)
            0: begin : gen_mode0
                assign y = a;
            end
            1: begin : gen_mode1
                assign y = ~a;
            end
            default: begin : gen_modedef
                assign y = 1'b0;
            end
        endcase
    endgenerate
endmodule
module big_width_case_module (input  logic [23:0] sel,
                              output logic        y);
    always_comb begin
        case (sel)
            24'hABCDEF: y = 1'b1;
            24'h123456: y = 1'b0;
            default   : y = 1'b0;
        endcase
    end
endmodule
