module unique_if_mod (
    input  logic [3:0] in_val,
    output logic       out_flag
);
    always_comb begin
        unique if (in_val == 4'd0)
            out_flag = 1'b0;
        else if (in_val == 4'd5)
            out_flag = 1'b1;
        else
            out_flag = 1'bx;
    end
endmodule
module priority_if_mod (
    input  logic signed [7:0] data_in,
    output logic              sign_bit
);
    always_comb begin
        priority if (data_in == 8'sd0)
            sign_bit = 1'b0;
        else if (data_in < 0)
            sign_bit = 1'b1;
        else
            sign_bit = data_in[7]; 
    end
endmodule
module unique_case_mod (
    input  logic [1:0] sel,
    output logic [3:0] mux_out
);
    always_comb begin
        unique case (sel)
            2'd0:          mux_out = 4'd1;
            2'd1:          mux_out = 4'd2;
            2'd2, 2'd3:    mux_out = 4'd3;
            default:       mux_out = 4'd0;
        endcase
    end
endmodule
module priority_case_inside_mod (
    input  logic [3:0] value,
    output logic [1:0] category
);
    always_comb begin
        priority case (value) inside
            4'd0:                    category = 2'd0;
            [4'd1:4'd3]:             category = 2'd1;
            [4'd4:4'd6]:             category = 2'd2;
            default:                 category = 2'd3;
        endcase
    end
endmodule
module casez_casex_mod (
    input  logic [3:0] opcode,
    output logic       action
);
    always_comb begin
        casez (opcode)
            4'b1z?? : action = 1'b1;   
            4'b1?1? : action = 1'b0;   
            default : action = 1'bx;
        endcase
    end
endmodule
module enum_case_mod (
    input  logic [1:0] st_in,
    output logic       enable
);
    typedef enum logic [1:0] {IDLE = 2'd0, RUN = 2'd1, STOP = 2'd2, ERR = 2'd3} state_t;
    state_t state;
    always_comb state = state_t'(st_in);
    always_comb begin : enum_case_block
        unique case (state)
            IDLE : enable = 1'b0;
            RUN  : enable = 1'b1;
            STOP : enable = 1'b0;
            default : enable = 1'b0;   
        endcase
    end
endmodule
module inside_if_mod (
    input  logic [3:0] test_val,
    output logic       hit
);
    always_comb begin
        if (test_val inside {4'd1, 4'd3, 4'd5})
            hit = 1'b1;
        else
            hit = 1'b0;
    end
endmodule
