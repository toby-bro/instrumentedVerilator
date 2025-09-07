module basic_case_and_comb (
    input [1:0] sel_in,
    input logic [7:0] data_in,
    output logic [7:0] out_data
);
    always_comb begin
        case (sel_in)
            2'b00: out_data = data_in + 1;
            2'b01: out_data = data_in - 1;
            2'b10: out_data = data_in * 2;
            default: out_data = data_in;
        endcase
    end
endmodule
module casex_casez_wildcards (
    input [3:0] sel_in,
    input logic [7:0] data_in,
    output logic [7:0] out_data_x,
    output logic [7:0] out_data_z
);
    always_comb begin
        casex (sel_in)
            4'b000x: out_data_x = data_in + 10;
            4'b0010: out_data_x = data_in + 20;
            4'b01x0: out_data_x = data_in + 30;
            4'b1x01: out_data_x = data_in + 40;
            default: out_data_x = data_in;
        endcase
    end
    always_comb begin
        casez (sel_in)
            4'b000z: out_data_z = data_in - 10;
            4'b001?: out_data_z = data_in - 20;
            4'b01x?: out_data_z = data_in - 30;
            4'b1??1: out_data_z = data_in - 40;
            default: out_data_z = data_in;
        endcase
    end
endmodule
module case_inside_and_large_items (
    input [7:0] value_in,
    output logic [7:0] result_out
);
    always_comb begin
        case (value_in) inside
            {8'h00, 8'h01}: result_out = value_in + 100;
            {8'h02, 8'h03, 8'h04}: result_out = value_in - 50;
            {8'h05, 8'h06, 8'h07, 8'h08}: result_out = value_in * 2;
            {8'h09, 8'h0A, 8'h0B, 8'h0C, 8'h0D}: result_out = value_in / 2;
            {8'h10, 8'h11, 8'h12, 8'h13, 8'h14, 8'h15}: result_out = value_in + 5;
            {8'h20, 8'h21, 8'h22, 8'h23, 8'h24, 8'h25, 8'h26}: result_out = value_in - 5;
            {8'h30, 8'h31, 8'h32, 8'h33, 8'h34, 8'h35, 8'h36, 8'h37}: result_out = value_in * 3;
            8'h40: result_out = 8'hF0;
            8'h41: result_out = 8'hF1;
            8'h42: result_out = 8'hF2;
            8'h43: result_out = 8'hF3;
            8'h44: result_out = 8'hF4;
            8'h45: result_out = 8'hF5;
            8'h46: result_out = 8'hF6;
            8'h47: result_out = 8'hF7;
            8'h48: result_out = 8'hF8;
            8'h49: result_out = 8'hF9;
            8'h4A: result_out = 8'hFA;
            8'h4B: result_out = 8'hFB;
            8'h4C: result_out = 8'hFC;
            8'h4D: result_out = 8'hFD;
            8'h4E: result_out = 8'hFE;
            8'h4F: result_out = 8'hFF;
            default: result_out = 8'hAA;
        endcase
    end
endmodule
module priority_unique_incomplete (
    input [2:0] sel_val,
    input logic [7:0] in_data_p,
    input logic [7:0] in_data_u,
    output logic [7:0] out_data_p,
    output logic [7:0] out_data_u,
    output logic [7:0] out_data_overlap_warn
);
    always_comb begin
        priority case (sel_val)
            3'b001: out_data_p = in_data_p + 1;
            3'b0x1: out_data_p = in_data_p + 2;
            3'b01x: out_data_p = in_data_p + 3;
            3'b100: out_data_p = in_data_p + 4;
            3'b1x0: out_data_p = in_data_p + 5;
            default: out_data_p = in_data_p;
        endcase
    end
    always_comb begin
        unique case (sel_val)
            3'b000: out_data_u = in_data_u + 10;
            3'b001: out_data_u = in_data_u + 11;
            3'b010: out_data_u = in_data_u + 12;
            3'b011: out_data_u = in_data_u + 13;
            3'b101: out_data_u = in_data_u + 15;
            3'b110: out_data_u = in_data_u + 16;
            3'b111: out_data_u = in_data_u + 17;
        endcase
    end
    always_comb begin
        case (sel_val)
            3'b001: out_data_overlap_warn = in_data_u + 10;
            3'b0x1: out_data_overlap_warn = in_data_u + 20;
            default: out_data_overlap_warn = 8'h00;
        endcase
    end
endmodule
module enum_case_check (
    input [1:0] state_in,
    output logic [7:0] state_info
);
    typedef enum logic [1:0] {
        IDLE = 2'b00,
        SETUP = 2'b01,
        ACTIVE = 2'b10,
        DONE = 2'b11
    } FSM_STATE;
    FSM_STATE current_state;
    always_comb begin
        current_state = FSM_STATE'(state_in);
        unique0 case (current_state)
            IDLE: state_info = 8'h00;
            SETUP: state_info = 8'h01;
            DONE: state_info = 8'h03;
        endcase
    end
endmodule
module fast_case_tree (
    input [3:0] sel_small,
    output logic [7:0] data_out_fast
);
    always_comb begin
        case (sel_small)
            4'b0000: data_out_fast = 8'h00;
            4'b0001: data_out_fast = 8'h01;
            4'b0010: data_out_fast = 8'h02;
            4'b0011: data_out_fast = 8'h03;
            4'b0100: data_out_fast = 8'h04;
            4'b0101: data_out_fast = 8'h05;
            4'b0110: data_out_fast = 8'h06;
            4'b0111: data_out_fast = 8'h07;
            4'b1000: data_out_fast = 8'h08;
            4'b1001: data_out_fast = 8'h09;
            4'b1010: data_out_fast = 8'h0A;
            4'b1011: data_out_fast = 8'h0B;
            4'b1100: data_out_fast = 8'h0C;
            4'b1101: data_out_fast = 8'h0D;
            4'b1110: data_out_fast = 8'h0E;
            4'b1111: data_out_fast = 8'h0F;
        endcase
    end
endmodule
module always_ff_with_case (
    input clk,
    input rst_n,
    input [1:0] op_code,
    input [7:0] data_in_ff,
    output logic [7:0] reg_out
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            reg_out <= 8'h00;
        end else begin
            case (op_code)
                2'b00: reg_out <= data_in_ff;
                2'b01: reg_out <= data_in_ff + 1;
                2'b10: reg_out <= data_in_ff - 1;
                default: reg_out <= reg_out;
            endcase
        end
    end
endmodule
module case_with_x_lint_warn (
    input [1:0] sel,
    input logic [7:0] din,
    output logic [7:0] dout
);
    always_comb begin
        case (sel)
            2'b00: dout = din + 1;
            2'b01: dout = din + 2;
            2'b1x: dout = din + 3;
            default: dout = din;
        endcase
    end
endmodule
