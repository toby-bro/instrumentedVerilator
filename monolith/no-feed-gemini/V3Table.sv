module mod_optimizable_arith_logic (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    input logic [3:0] in_sel,
    output logic [7:0] out_sum,
    output logic [7:0] out_diff,
    output logic [15:0] out_concat
);
    always_comb begin
        out_sum = in_a + in_b;
        out_diff = in_a - in_b;
        case (in_sel)
            4'd0: out_concat = {in_a, in_b};
            4'd1: out_concat = {in_b, in_a};
            default: out_concat = {in_a[3:0], in_b[3:0], in_a[7:4], in_b[7:4]};
        endcase
    end
endmodule
module mod_conditional_unassigned (
    input logic [3:0] val_in,
    input logic       cond_x,
    input logic       cond_y,
    output logic [3:0] out_x,
    output logic [3:0] out_y,
    output logic [3:0] out_z
);
    always_comb begin
        out_x = val_in + 1;
        if (cond_x) begin
            out_y = val_in * 2;
        end
        if (cond_x && !cond_y) begin
            out_z = val_in | 4'b1100;
        end else if (!cond_x && cond_y) begin
            out_z = val_in & 4'b0011;
        end
    end
endmodule
module mod_non_blocking_assigns (
    input logic clk,
    input logic rst_n,
    input logic [2:0] data_in,
    output logic [2:0] data_out_q,
    output logic [2:0] data_out_qq
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_out_q  <= 3'b000;
            data_out_qq <= 3'b000;
        end else begin
            data_out_q  <= data_in;
            data_out_qq <= data_out_q;
        end
    end
endmodule
module mod_too_much_space (
    input logic [17:0] in_wide,
    output logic [31:0] out_wide
);
    always_comb begin
        out_wide = {in_wide[17:0], in_wide[17:0][7:0]};
    end
endmodule
module mod_too_few_nodes (
    input logic [3:0] in_small,
    output logic [3:0] out_small
);
    always_comb begin
        out_small = in_small + 1;
    end
endmodule
module mod_bad_spacetime_tradeoff (
    input logic [15:0] in_data,
    output logic [0:0] out_bit
);
    always_comb begin
        out_bit = in_data[0] ^ in_data[15];
    end
endmodule
module mod_x_z_output (
    input logic [3:0] input_val,
    input logic       enable_x,
    input logic       enable_z,
    output logic [3:0] result_out
);
    always_comb begin
        if (enable_x) begin
            result_out = 4'bxxxx;
        end else if (enable_z) begin
            result_out = 4'bzzzz;
        end else begin
            result_out = input_val + 1;
        end
    end
endmodule
module mod_assign_stmt (
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    assign data_out = data_in + 8'd5;
endmodule
module mod_data_types (
    input logic [7:0] in_byte,
    input logic [31:0] in_int,
    output byte out_byte,
    output int out_int,
    output longint out_longint
);
    real dummy_real;
    string dummy_string;
    always_comb begin
        out_byte    = in_byte + 1;
        out_int     = in_int + 10;
        out_longint = {in_int, in_byte, in_byte, in_byte, 8'h00};
        dummy_real = $itor(in_int);
        dummy_string = "hello";
    end
endmodule
module mod_no_outputs (
    input logic [7:0] in_dummy
);
    always_comb begin
        logic [7:0] internal_var;
        internal_var = in_dummy * 2;
    end
endmodule
module mod_no_inputs (
    output logic [7:0] out_dummy
);
    always_comb begin
        out_dummy = 8'hAA;
    end
endmodule
module mod_impure_logic (
    input  logic [7:0] in_val,
    output logic [7:0] out_val
);
    real my_real_var;
    always_comb begin
        my_real_var = $itor(in_val);
        my_real_var = my_real_var * 2.5;
        out_val = $rtoi(my_real_var);
    end
endmodule
module mod_coverage_sensitive (
    input logic [3:0] in_a_cov,
    input logic [3:0] in_b_cov,
    input logic [1:0] sel_cov,
    output logic [7:0] out_cov
);
    always_comb begin
        out_cov = 8'h00;
        if (in_a_cov > 4'd8) begin
            out_cov[3:0] = in_a_cov;
            if (in_b_cov < 4'd4) begin
                out_cov[7:4] = in_b_cov;
            end else begin
                out_cov[7:4] = in_a_cov;
            end
        end else begin
            case (sel_cov)
                2'b00: out_cov = {in_a_cov, in_b_cov};
                2'b01: out_cov = {in_b_cov, in_a_cov};
                2'b10: out_cov = in_a_cov + in_b_cov;
                default: out_cov = 8'hFF;
            endcase
        end
    end
endmodule
module mod_bit_part_selects (
    input logic [15:0] in_vec,
    input logic [3:0] index,
    output logic       out_bit,
    output logic [7:0] out_byte_part,
    output logic [3:0] out_slice
);
    always_comb begin
        out_bit       = in_vec[index];
        out_byte_part = in_vec[15:8];
        out_slice     = in_vec[index+:4];
    end
endmodule
