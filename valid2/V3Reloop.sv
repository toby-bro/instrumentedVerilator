module reloop_neg_offset (
    input  logic [31:0] src [0:16],
    output logic [31:0] dst [0:15]
);
    always_comb begin
        dst[0]  = src[1];
        dst[1]  = src[2];
        dst[2]  = src[3];
        dst[3]  = src[4];
        dst[4]  = src[5];
        dst[5]  = src[6];
        dst[6]  = src[7];
        dst[7]  = src[8];
        dst[8]  = src[9];
        dst[9]  = src[10];
        dst[10] = src[11];
        dst[11] = src[12];
        dst[12] = src[13];
        dst[13] = src[14];
        dst[14] = src[15];
        dst[15] = src[16];
    end
endmodule
module reloop_pos_offset (
    input  logic [31:0] src [0:16],
    output logic [31:0] dst [0:16]
);
    always_comb begin
        dst[1]  = src[0];
        dst[2]  = src[1];
        dst[3]  = src[2];
        dst[4]  = src[3];
        dst[5]  = src[4];
        dst[6]  = src[5];
        dst[7]  = src[6];
        dst[8]  = src[7];
        dst[9]  = src[8];
        dst[10] = src[9];
        dst[11] = src[10];
        dst[12] = src[11];
        dst[13] = src[12];
        dst[14] = src[13];
        dst[15] = src[14];
        dst[16] = src[15];
        dst[0]  = src[0];   
    end
endmodule
module reloop_const_assign (
    input  logic dummy_in,
    output logic [31:0] arr [0:15]
);
    always_comb begin
        arr[0]  = 32'hDEAD_BEEF;
        arr[1]  = 32'hDEAD_BEEF;
        arr[2]  = 32'hDEAD_BEEF;
        arr[3]  = 32'hDEAD_BEEF;
        arr[4]  = 32'hDEAD_BEEF;
        arr[5]  = 32'hDEAD_BEEF;
        arr[6]  = 32'hDEAD_BEEF;
        arr[7]  = 32'hDEAD_BEEF;
        arr[8]  = 32'hDEAD_BEEF;
        arr[9]  = 32'hDEAD_BEEF;
        arr[10] = 32'hDEAD_BEEF;
        arr[11] = 32'hDEAD_BEEF;
        arr[12] = 32'hDEAD_BEEF;
        arr[13] = 32'hDEAD_BEEF;
        arr[14] = 32'hDEAD_BEEF;
        arr[15] = 32'hDEAD_BEEF;
    end
endmodule
module reloop_offset_two (
    input  logic [31:0] src [0:17],
    output logic [31:0] dst [0:15]
);
    always_comb begin
        dst[0]  = src[2];
        dst[1]  = src[3];
        dst[2]  = src[4];
        dst[3]  = src[5];
        dst[4]  = src[6];
        dst[5]  = src[7];
        dst[6]  = src[8];
        dst[7]  = src[9];
        dst[8]  = src[10];
        dst[9]  = src[11];
        dst[10] = src[12];
        dst[11] = src[13];
        dst[12] = src[14];
        dst[13] = src[15];
        dst[14] = src[16];
        dst[15] = src[17];
    end
endmodule
module reloop_const_zero (
    input  logic enable,
    output logic [7:0] small_arr [0:31]
);
    always_comb begin
        small_arr[0]  = 8'h00;
        small_arr[1]  = 8'h00;
        small_arr[2]  = 8'h00;
        small_arr[3]  = 8'h00;
        small_arr[4]  = 8'h00;
        small_arr[5]  = 8'h00;
        small_arr[6]  = 8'h00;
        small_arr[7]  = 8'h00;
        small_arr[8]  = 8'h00;
        small_arr[9]  = 8'h00;
        small_arr[10] = 8'h00;
        small_arr[11] = 8'h00;
        small_arr[12] = 8'h00;
        small_arr[13] = 8'h00;
        small_arr[14] = 8'h00;
        small_arr[15] = 8'h00;
        small_arr[16] = 8'h00;
        small_arr[17] = 8'h00;
        small_arr[18] = 8'h00;
        small_arr[19] = 8'h00;
        small_arr[20] = 8'h00;
        small_arr[21] = 8'h00;
        small_arr[22] = 8'h00;
        small_arr[23] = 8'h00;
        small_arr[24] = 8'h00;
        small_arr[25] = 8'h00;
        small_arr[26] = 8'h00;
        small_arr[27] = 8'h00;
        small_arr[28] = 8'h00;
        small_arr[29] = 8'h00;
        small_arr[30] = 8'h00;
        small_arr[31] = 8'h00;
    end
endmodule
module reloop_offset_three (
    input  logic [31:0] src [0:19],
    output logic [31:0] dst [0:16]
);
    always_comb begin
        dst[0]  = src[3];
        dst[1]  = src[4];
        dst[2]  = src[5];
        dst[3]  = src[6];
        dst[4]  = src[7];
        dst[5]  = src[8];
        dst[6]  = src[9];
        dst[7]  = src[10];
        dst[8]  = src[11];
        dst[9]  = src[12];
        dst[10] = src[13];
        dst[11] = src[14];
        dst[12] = src[15];
        dst[13] = src[16];
        dst[14] = src[17];
        dst[15] = src[18];
        dst[16] = src[19];
    end
endmodule
