module snippet (
    input wire clk,
    input logic [7:0] inj_in_a_g_1755007821168_53,
    input logic [7:0] inj_in_b_g_1755007821168_255,
    input int inj_input_int_1755007821168_552,
    input logic [31:0] inj_p_in1_1755007821169_514,
    input logic [31:0] inj_p_in2_1755007821169_731,
    input logic [1:0] inj_p_mode_1755007821169_677,
    input wire reset,
    output logic [7:0] inj_out_p_g_1755007821168_69,
    output logic [7:0] inj_out_q_g_1755007821168_175,
    output int inj_output_int_1755007821168_202,
    output logic [31:0] inj_p_out_1755007821169_434
);
    // BEGIN: split_reorder_blocking_ts1755007821168
    logic [7:0] mid_x_g_ts1755007821168;
    logic [7:0] mid_y_g_ts1755007821168;
        // BEGIN: func_macro_args_ts1755007821169
        `define ADD(a, b)       ((a) + (b))
        `define SUBTRACT(x, y)  ((x) - (y))
        localparam int P1_ADD = `ADD(10, 20);
        int p2_sub_var_ts1755007821169;
            // BEGIN: more_procedural_ts1755007821169
            always_comb begin
                case (inj_p_mode_1755007821169_677)
                    2'b00: inj_p_out_1755007821169_434 = (inj_p_in1_1755007821169_514 + inj_p_in2_1755007821169_731) * 2;
                    2'b01: inj_p_out_1755007821169_434 = (inj_p_in1_1755007821169_514 - inj_p_in2_1755007821169_731) / 3; 
                    2'b10: inj_p_out_1755007821169_434 = (inj_p_in1_1755007821169_514 << 4) | (inj_p_in2_1755007821169_731 >> 2);
                    default: inj_p_out_1755007821169_434 = ~(inj_p_in1_1755007821169_514 ^ inj_p_in2_1755007821169_731) + 1;
                endcase
            end
            // END: more_procedural_ts1755007821169

        always_comb begin
            p2_sub_var_ts1755007821169 = `SUBTRACT(50, inj_input_int_1755007821168_552);
        end
        assign inj_output_int_1755007821168_202 = P1_ADD + p2_sub_var_ts1755007821169;
        // END: func_macro_args_ts1755007821169

    always @(*) begin
        mid_x_g_ts1755007821168 = inj_in_a_g_1755007821168_53 * 2;
        mid_y_g_ts1755007821168 = mid_x_g_ts1755007821168 + inj_in_b_g_1755007821168_255;
        inj_out_p_g_1755007821168_69 = mid_y_g_ts1755007821168 - 1;
        inj_out_q_g_1755007821168_175 = mid_x_g_ts1755007821168 / 2;
    end
    // END: split_reorder_blocking_ts1755007821168
endmodule

