module reloop_test;
  // Arrays for testing
  reg [7:0] array1[0:63];
  reg [7:0] array2[0:63];
  reg [7:0] array3[0:63];
  reg [31:0] big_array[0:127];
  
  // Vector for testing
  reg [63:0] vector1;
  reg [63:0] vector2;
  
  initial begin
    // Case 1: Sequential assignments to array elements (should be converted to a loop)
    array1[0] = 8'h10;
    array1[1] = 8'h11;
    array1[2] = 8'h12;
    array1[3] = 8'h13;
    array1[4] = 8'h14;
    array1[5] = 8'h15;
    array1[6] = 8'h16;
    array1[7] = 8'h17;
    array1[8] = 8'h18;
    array1[9] = 8'h19;
    array1[10] = 8'h1A;
    array1[11] = 8'h1B;
    array1[12] = 8'h1C;
    array1[13] = 8'h1D;
    array1[14] = 8'h1E;
    array1[15] = 8'h1F;
    
    // Case 2: Array to array assignments with positive offset (should be converted to a loop)
    array2[0] = array1[5];
    array2[1] = array1[6];
    array2[2] = array1[7];
    array2[3] = array1[8];
    array2[4] = array1[9];
    array2[5] = array1[10];
    array2[6] = array1[11];
    array2[7] = array1[12];
    array2[8] = array1[13];
    array2[9] = array1[14];
    array2[10] = array1[15];
    
    // Case 3: Array to array assignments with negative offset
    array3[10] = array3[5];
    array3[11] = array3[6];
    array3[12] = array3[7];
    array3[13] = array3[8];
    array3[14] = array3[9];
    array3[15] = array3[10];
    array3[16] = array3[11];
    array3[17] = array3[12];
    array3[18] = array3[13];
    array3[19] = array3[14];
    
    // Case 4: Non-sequential assignments (should not be converted)
    big_array[0] = 32'h00000001;
    big_array[2] = 32'h00000002;
    big_array[4] = 32'h00000003;
    
    // Case 5: Sequential assignments interleaved with other statements (should not be converted)
    array1[20] = 8'h20;
    $display("Interleaved statement");
    array1[21] = 8'h21;
    $display("Another interleaved statement");
    array1[22] = 8'h22;
    
    // Case 6: Large sequential assignment to test the reloop limit
    // This should be converted if v3Global.opt.reloopLimit() is smaller than 32
    big_array[32] = 32'hAA000000;
    big_array[33] = 32'hAA000001;
    big_array[34] = 32'hAA000002;
    big_array[35] = 32'hAA000003;
    big_array[36] = 32'hAA000004;
    big_array[37] = 32'hAA000005;
    big_array[38] = 32'hAA000006;
    big_array[39] = 32'hAA000007;
    big_array[40] = 32'hAA000008;
    big_array[41] = 32'hAA000009;
    big_array[42] = 32'hAA00000A;
    big_array[43] = 32'hAA00000B;
    big_array[44] = 32'hAA00000C;
    big_array[45] = 32'hAA00000D;
    big_array[46] = 32'hAA00000E;
    big_array[47] = 32'hAA00000F;
    big_array[48] = 32'hAA000010;
    big_array[49] = 32'hAA000011;
    big_array[50] = 32'hAA000012;
    big_array[51] = 32'hAA000013;
    big_array[52] = 32'hAA000014;
    big_array[53] = 32'hAA000015;
    big_array[54] = 32'hAA000016;
    big_array[55] = 32'hAA000017;
    big_array[56] = 32'hAA000018;
    big_array[57] = 32'hAA000019;
    big_array[58] = 32'hAA00001A;
    big_array[59] = 32'hAA00001B;
    big_array[60] = 32'hAA00001C;
    big_array[61] = 32'hAA00001D;
    big_array[62] = 32'hAA00001E;
    big_array[63] = 32'hAA00001F;
    
    // Case 7: Constant assignments to vector bits (should be converted)
    vector1[0] = 1'b0;
    vector1[1] = 1'b1;
    vector1[2] = 1'b0;
    vector1[3] = 1'b1;
    vector1[4] = 1'b0;
    vector1[5] = 1'b1;
    vector1[6] = 1'b0;
    vector1[7] = 1'b1;
    vector1[8] = 1'b0;
    vector1[9] = 1'b1;
    
    // Case 8: Copy one vector to another with offset
    vector2[0] = vector1[5];
    vector2[1] = vector1[6];
    vector2[2] = vector1[7];
    vector2[3] = vector1[8];
    vector2[4] = vector1[9];
    vector2[5] = vector1[10];
    vector2[6] = vector1[11];
    vector2[7] = vector1[12];
    vector2[8] = vector1[13];
    vector2[9] = vector1[14];
    
    // Display results to prevent optimization removal
    $display("Test complete");
  end
endmodule
