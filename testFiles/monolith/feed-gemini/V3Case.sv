module case_fast_opt_test (
    input logic [3:0] in_sel,
    output logic [7:0] out_data
);
always_comb begin
    case (in_sel)
        4'b0000: out_data = 8'hAA;
        4'b0001: out_data = 8'hAA;
        4'b0010: out_data = 8'hBB;
        4'b0011: out_data = 8'hBB;
        4'b0100: out_data = 8'hCC;
        4'b0101: out_data = 8'hDD;
        4'b0110: out_data = 8'hCC;
        4'b0111: out_data = 8'hDD;
        4'b1000: out_data = 8'hEE;
        4'b1001: out_data = 8'hFF;
        4'b1010: out_data = 8'hEE;
        4'b1011: out_data = 8'hFF;
        4'b1100: out_data = 8'h11;
        4'b1101: out_data = 8'h22;
        4'b1110: out_data = 8'h33;
        4'b1111: out_data = 8'h44;
    endcase
end
endmodule
module case_priority_enum_incomplete (
    input logic [1:0] in_enum_val,
    output logic out_flag
);
typedef enum logic [1:0] {
    STATE_A = 2'b00,
    STATE_B = 2'b01,
    STATE_C = 2'b10,
    STATE_D = 2'b11
} my_state_t;
my_state_t current_state;
assign current_state = my_state_t'(in_enum_val);
always_comb begin
    out_flag = 1'b0;
    priority case (current_state)
        STATE_A: out_flag = 1'b1;
        STATE_B: out_flag = 1'b0;
        default: out_flag = 1'b0;
    endcase
end
endmodule
module casex_xz_conditions (
    input logic [3:0] in_val_casex,
    output logic [7:0] out_res_casex
);
always_comb begin
    casex (in_val_casex)
        4'b101x: out_res_casex = 8'h11;
        4'b01z0: out_res_casex = 8'h22;
        4'bxxxx: out_res_casex = 8'hFF;
        default: out_res_casex = 8'h00;
    endcase
end
endmodule
module casez_x_condition_lint (
    input logic [2:0] in_val_casez,
    output logic [7:0] out_res_casez
);
always_comb begin
    casez (in_val_casez)
        3'b1x0: out_res_casez = 8'hAA;
        3'b0z1: out_res_casez = 8'hBB;
        3'b11?: out_res_casez = 8'hCC;
        default: out_res_casez = 8'h00;
    endcase
end
endmodule
module case_inside_range_direct (
    input logic [4:0] in_val_inside_direct,
    output logic [7:0] out_res_inside_direct
);
always_comb begin
    case (in_val_inside_direct) inside
        {5'd0, 5'd1, 5'd2}: out_res_inside_direct = 8'hAA;
        [5'd3:5'd5], 5'd7: out_res_inside_direct = 8'hBB;
        {5'd8, 5'd9}: out_res_inside_direct = 8'hCC;
        {5'b1x010}: out_res_inside_direct = 8'hDD;
        default: out_res_inside_direct = 8'hFF;
    endcase
end
endmodule
module case_large_complicated (
    input logic [18:0] in_large_sel,
    output logic [7:0] out_large_data
);
always_comb begin
    case (in_large_sel)
        19'd0: out_large_data = 8'h00;
        19'd1: out_large_data = 8'h01;
        19'd2: out_large_data = 8'h02;
        19'd3: out_large_data = 8'h03;
        19'd4: out_large_data = 8'h04;
        19'd5: out_large_data = 8'h05;
        19'd6: out_large_data = 8'h06;
        19'd7: out_large_data = 8'h07;
        19'd8: out_large_data = 8'h08;
        19'd9: out_large_data = 8'h09;
        19'd10: out_large_data = 8'h0A;
        19'd11: out_large_data = 8'h0B;
        19'd12: out_large_data = 8'h0C;
        19'd13: out_large_data = 8'h0D;
        19'd14: out_large_data = 8'h0E;
        19'd15: out_large_data = 8'h0F;
        19'd16: out_large_data = 8'h10;
        19'd17: out_large_data = 8'h11;
        19'd18: out_large_data = 8'h12;
        19'd19: out_large_data = 8'h13;
        19'd20: out_large_data = 8'h14;
        default: out_large_data = 8'hFF;
    endcase
end
endmodule
module case_overlap_warn (
    input logic [2:0] in_overlap_sel,
    output logic [7:0] out_overlap_data
);
always_comb begin
    case (in_overlap_sel)
        3'd0: out_overlap_data = 8'h10;
        3'd1: out_overlap_data = 8'h20;
        3'd0: out_overlap_data = 8'h30;
        3'd2: out_overlap_data = 8'h40;
        3'd3: out_overlap_data = 8'h50;
        3'd3: out_overlap_data = 8'h60;
        default: out_overlap_data = 8'hFF;
    endcase
end
endmodule
module gen_case_x_lint (
    input logic in_dummy_input,
    output logic out_gen_flag
);
parameter [1:0] GEN_SEL_PARAM = 2'b01;
genvar i;
generate
    case (GEN_SEL_PARAM)
        2'b0X: begin
            always_comb begin
                out_gen_flag = in_dummy_input;
            end
        end
        2'b10: begin
            always_comb begin
                out_gen_flag = ~in_dummy_input;
            end
        end
        default: begin
            always_comb begin
                out_gen_flag = 1'b0;
            end
        end
    endcase
endgenerate
endmodule
module multiple_default_lint (
    input logic [1:0] in_multi_default_sel,
    output logic out_multi_default_data
);
always_comb begin
    out_multi_default_data = 1'b0;
    case (in_multi_default_sel)
        2'b00: out_multi_default_data = 1'b1;
        default: out_multi_default_data = 1'b0;
        2'b01: out_multi_default_data = 1'b1;
    endcase
end
endmodule
module case_all_covered_no_default (
    input logic [1:0] in_all_covered_sel,
    output logic [7:0] out_all_covered_data
);
always_comb begin
    case (in_all_covered_sel)
        2'b00: out_all_covered_data = 8'h11;
        2'b01: out_all_covered_data = 8'h22;
        2'b10: out_all_covered_data = 8'h33;
        2'b11: out_all_covered_data = 8'h44;
    endcase
end
endmodule
module plain_case_x_lint (
    input logic [2:0] in_plain_sel,
    output logic out_plain_data
);
always_comb begin
    out_plain_data = 1'b0;
    case (in_plain_sel)
        3'b1x0: out_plain_data = 1'b1;
        3'b011: out_plain_data = 1'b0;
        default: out_plain_data = 1'b0;
    endcase
end
endmodule
