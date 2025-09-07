module simple_for_unroll (
    input logic [7:0] in_data,
    output logic [7:0] out_sum
);
    logic [7:0] sum;
    logic [3:0] i;
    initial begin
        sum = 0;
        for (i = 0; i < 3; i = i + 1) begin
            sum = sum + in_data + i;
        end
        out_sum = sum;
    end
endmodule
module for_var_assign_inside (
    input logic [7:0] in_data,
    output logic [7:0] out_result
);
    logic [7:0] result;
    logic [3:0] idx;
    initial begin
        result = 0;
        for (idx = 0; idx < 5; idx = idx + 1) begin
            result = result + in_data;
            if (idx == 2) begin
                idx = 4; 
            end
        end
        out_result = result;
    end
endmodule
module for_fork_inside (
    input logic [7:0] in_val,
    output logic [7:0] out_accum
);
    logic [7:0] accum_val;
    logic [3:0] k;
    initial begin
        accum_val = 0;
        for (k = 0; k < 2; k = k + 1) begin
            accum_val = accum_val + in_val;
            fork : my_fork_block
                accum_val = accum_val + 1;
            join_none
        end
        out_accum = accum_val;
    end
endmodule
module for_unroll_disable (
    input logic [7:0] val_in,
    output logic [7:0] val_out
);
    logic [7:0] temp_val;
    logic [3:0] j;
    initial begin
        temp_val = 0;
        for (j = 0; j < 4; j = j + 1) begin
            temp_val = temp_val + val_in + j;
        end
        val_out = temp_val;
    end
endmodule
module for_non_const_init (
    input logic [7:0] init_val_in,
    output logic [7:0] final_res
);
    logic [7:0] res;
    logic [3:0] m;
    logic [7:0] start_val; 
    initial begin
        start_val = init_val_in;
        res = 0;
        for (m = start_val; m < start_val + 3; m = m + 1) begin
            res = res + m;
        end
        final_res = res;
    end
endmodule
module for_large_body (
    input logic [7:0] data_a,
    output logic [7:0] data_b
);
    logic [7:0] reg_sum;
    logic [3:0] n;
    logic [7:0] temp_regs [0:99]; 
    initial begin
        reg_sum = 0;
        for (n = 0; n < 2; n = n + 1) begin 
            reg_sum = reg_sum + data_a;
            temp_regs[0] = data_a + n;
            temp_regs[1] = data_a + n + 1;
            temp_regs[2] = data_a + n + 2;
            temp_regs[3] = data_a + n + 3;
            temp_regs[4] = data_a + n + 4;
            temp_regs[5] = data_a + n + 5;
            temp_regs[6] = data_a + n + 6;
            temp_regs[7] = data_a + n + 7;
            temp_regs[8] = data_a + n + 8;
            temp_regs[9] = data_a + n + 9;
            temp_regs[10] = data_a + n + 10;
            temp_regs[11] = data_a + n + 11;
            temp_regs[12] = data_a + n + 12;
            temp_regs[13] = data_a + n + 13;
            temp_regs[14] = data_a + n + 14;
            temp_regs[15] = data_a + n + 15;
            temp_regs[16] = data_a + n + 16;
            temp_regs[17] = data_a + n + 17;
            temp_regs[18] = data_a + n + 18;
            temp_regs[19] = data_a + n + 19;
            temp_regs[20] = data_a + n + 20;
            temp_regs[21] = data_a + n + 21;
            temp_regs[22] = data_a + n + 22;
            temp_regs[23] = data_a + n + 23;
            temp_regs[24] = data_a + n + 24;
            temp_regs[25] = data_a + n + 25;
            temp_regs[26] = data_a + n + 26;
            temp_regs[27] = data_a + n + 27;
            temp_regs[28] = data_a + n + 28;
            temp_regs[29] = data_a + n + 29;
            temp_regs[30] = data_a + n + 30;
            temp_regs[31] = data_a + n + 31;
            temp_regs[32] = data_a + n + 32;
            temp_regs[33] = data_a + n + 33;
            temp_regs[34] = data_a + n + 34;
            temp_regs[35] = data_a + n + 35;
            temp_regs[36] = data_a + n + 36;
            temp_regs[37] = data_a + n + 37;
            temp_regs[38] = data_a + n + 38;
            temp_regs[39] = data_a + n + 39;
            temp_regs[40] = data_a + n + 40;
            temp_regs[41] = data_a + n + 41;
            temp_regs[42] = data_a + n + 42;
            temp_regs[43] = data_a + n + 43;
            temp_regs[44] = data_a + n + 44;
            temp_regs[45] = data_a + n + 45;
            temp_regs[46] = data_a + n + 46;
            temp_regs[47] = data_a + n + 47;
            temp_regs[48] = data_a + n + 48;
            temp_regs[49] = data_a + n + 49;
            temp_regs[50] = data_a + n + 50;
            temp_regs[51] = data_a + n + 51;
            temp_regs[52] = data_a + n + 52;
            temp_regs[53] = data_a + n + 53;
            temp_regs[54] = data_a + n + 54;
            temp_regs[55] = data_a + n + 55;
            temp_regs[56] = data_a + n + 56;
            temp_regs[57] = data_a + n + 57;
            temp_regs[58] = data_a + n + 58;
            temp_regs[59] = data_a + n + 59;
            temp_regs[60] = data_a + n + 60;
            temp_regs[61] = data_a + n + 61;
            temp_regs[62] = data_a + n + 62;
            temp_regs[63] = data_a + n + 63;
            temp_regs[64] = data_a + n + 64;
            temp_regs[65] = data_a + n + 65;
            temp_regs[66] = data_a + n + 66;
            temp_regs[67] = data_a + n + 67;
            temp_regs[68] = data_a + n + 68;
            temp_regs[69] = data_a + n + 69;
            temp_regs[70] = data_a + n + 70;
            temp_regs[71] = data_a + n + 71;
            temp_regs[72] = data_a + n + 72;
            temp_regs[73] = data_a + n + 73;
            temp_regs[74] = data_a + n + 74;
            temp_regs[75] = data_a + n + 75;
            temp_regs[76] = data_a + n + 76;
            temp_regs[77] = data_a + n + 77;
            temp_regs[78] = data_a + n + 78;
            temp_regs[79] = data_a + n + 79;
            temp_regs[80] = data_a + n + 80;
            temp_regs[81] = data_a + n + 81;
            temp_regs[82] = data_a + n + 82;
            temp_regs[83] = data_a + n + 83;
            temp_regs[84] = data_a + n + 84;
            temp_regs[85] = data_a + n + 85;
            temp_regs[86] = data_a + n + 86;
            temp_regs[87] = data_a + n + 87;
            temp_regs[88] = data_a + n + 88;
            temp_regs[89] = data_a + n + 89;
            temp_regs[90] = data_a + n + 90;
            temp_regs[91] = data_a + n + 91;
            temp_regs[92] = data_a + n + 92;
            temp_regs[93] = data_a + n + 93;
            temp_regs[94] = data_a + n + 94;
            temp_regs[95] = data_a + n + 95;
            temp_regs[96] = data_a + n + 96;
            temp_regs[97] = data_a + n + 97;
            temp_regs[98] = data_a + n + 98;
            temp_regs[99] = data_a + n + 99;
        end
        data_b = reg_sum + temp_regs[0];
    end
endmodule
module simple_gen_for (
    input logic [7:0] data_input,
    output logic [7:0] data_output
);
    genvar g;
    logic [7:0] gen_sum;
    initial begin
        gen_sum = 0;
    end
    generate
        for (g = 0; g < 3; g++) begin : gen_block
            always_comb begin
                gen_sum = gen_sum + data_input + g;
            end
        end
    endgenerate
    assign data_output = gen_sum;
endmodule
module genfor_cond_zero (
    input logic in_enable,
    output logic out_flag
);
    genvar idx;
    logic flag_reg;
    initial begin
        flag_reg = 0;
    end
    generate
        for (idx = 0; 1'b0; idx++) begin : empty_gen
            always_comb begin
                flag_reg = in_enable; 
            end
        end
    endgenerate
    assign out_flag = flag_reg; 
endmodule
module genfor_non_genvar (
    input logic [7:0] val_in_a,
    output logic [7:0] val_out_b
);
    logic [3:0] loop_idx; 
    logic [7:0] final_val;
    initial begin
        final_val = 0;
    end
    generate
        for (loop_idx = 0; loop_idx < 2; loop_idx++) begin : bad_gen
            always_comb begin
                final_val = final_val + val_in_a;
            end
        end
    endgenerate
    assign val_out_b = final_val;
endmodule
module while_loop_like_for (
    input logic [7:0] input_a,
    output logic [7:0] output_b
);
    logic [7:0] current_val;
    logic [3:0] cnt;
    initial begin
        current_val = 0;
        cnt = 0; 
        while (cnt < 4) begin 
            current_val = current_val + input_a;
            cnt = cnt + 1; 
        end
        output_b = current_val;
    end
endmodule
