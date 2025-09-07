module deep_arith_module (
  input logic [7:0] in_val [0:300],
  output logic [15:0] out_sum
);
  function automatic logic [15:0] calculate_deep_sum(input logic [7:0] vals [0:300]);
    return vals[0] + vals[1] + vals[2] + vals[3] + vals[4] +
           vals[5] + vals[6] + vals[7] + vals[8] + vals[9] +
           vals[10] + vals[11] + vals[12] + vals[13] + vals[14] +
           vals[15] + vals[16] + vals[17] + vals[18] + vals[19] +
           vals[20] + vals[21] + vals[22] + vals[23] + vals[24] +
           vals[25] + vals[26] + vals[27] + vals[28] + vals[29] +
           vals[30] + vals[31] + vals[32] + vals[33] + vals[34] +
           vals[35] + vals[36] + vals[37] + vals[38] + vals[39] +
           vals[40] + vals[41] + vals[42] + vals[43] + vals[44] +
           vals[45] + vals[46] + vals[47] + vals[48] + vals[49] +
           vals[50] + vals[51] + vals[52] + vals[53] + vals[54] +
           vals[55] + vals[56] + vals[57] + vals[58] + vals[59] +
           vals[60] + vals[61] + vals[62] + vals[63] + vals[64] +
           vals[65] + vals[66] + vals[67] + vals[68] + vals[69] +
           vals[70] + vals[71] + vals[72] + vals[73] + vals[74] +
           vals[75] + vals[76] + vals[77] + vals[78] + vals[79] +
           vals[80] + vals[81] + vals[82] + vals[83] + vals[84] +
           vals[85] + vals[86] + vals[87] + vals[88] + vals[89] +
           vals[90] + vals[91] + vals[92] + vals[93] + vals[94] +
           vals[95] + vals[96] + vals[97] + vals[98] + vals[99] +
           vals[100] + vals[101] + vals[102] + vals[103] + vals[104] +
           vals[105] + vals[106] + vals[107] + vals[108] + vals[109] +
           vals[110] + vals[111] + vals[112] + vals[113] + vals[114] +
           vals[115] + vals[116] + vals[117] + vals[118] + vals[119] +
           vals[120] + vals[121] + vals[122] + vals[123] + vals[124] +
           vals[125] + vals[126] + vals[127] + vals[128] + vals[129] +
           vals[130] + vals[131] + vals[132] + vals[133] + vals[134] +
           vals[135] + vals[136] + vals[137] + vals[138] + vals[139] +
           vals[140] + vals[141] + vals[142] + vals[143] + vals[144] +
           vals[145] + vals[146] + vals[147] + vals[148] + vals[149] +
           vals[150] + vals[151] + vals[152] + vals[153] + vals[154] +
           vals[155] + vals[156] + vals[157] + vals[158] + vals[159] +
           vals[160] + vals[161] + vals[162] + vals[163] + vals[164] +
           vals[165] + vals[166] + vals[167] + vals[168] + vals[169] +
           vals[170] + vals[171] + vals[172] + vals[173] + vals[174] +
           vals[175] + vals[176] + vals[177] + vals[178] + vals[179] +
           vals[180] + vals[181] + vals[182] + vals[183] + vals[184] +
           vals[185] + vals[186] + vals[187] + vals[188] + vals[189] +
           vals[190] + vals[191] + vals[192] + vals[193] + vals[194] +
           vals[195] + vals[196] + vals[197] + vals[198] + vals[199] +
           vals[200] + vals[201] + vals[202] + vals[203] + vals[204] +
           vals[205] + vals[206] + vals[207] + vals[208] + vals[209] +
           vals[210] + vals[211] + vals[212] + vals[213] + vals[214] +
           vals[215] + vals[216] + vals[217] + vals[218] + vals[219] +
           vals[220] + vals[221] + vals[222] + vals[223] + vals[224] +
           vals[225] + vals[226] + vals[227] + vals[228] + vals[229] +
           vals[230] + vals[231] + vals[232] + vals[233] + vals[234] +
           vals[235] + vals[236] + vals[237] + vals[238] + vals[239] +
           vals[240] + vals[241] + vals[242] + vals[243] + vals[244] +
           vals[245] + vals[246] + vals[247] + vals[248] + vals[249] +
           vals[250] + vals[251] + vals[252] + vals[253] + vals[254] +
           vals[255] + vals[256] + vals[257] + vals[258] + vals[259] +
           vals[260] + vals[261] + vals[262] + vals[263] + vals[264] +
           vals[265] + vals[266] + vals[267] + vals[268] + vals[269] +
           vals[270] + vals[271] + vals[272] + vals[273] + vals[274] +
           vals[275] + vals[276] + vals[277] + vals[278] + vals[279] +
           vals[280] + vals[281] + vals[282] + vals[283] + vals[284] +
           vals[285] + vals[286] + vals[287] + vals[288] + vals[289] +
           vals[290] + vals[291] + vals[292] + vals[293] + vals[294] +
           vals[295] + vals[296] + vals[297] + vals[298] + vals[299] +
           vals[300];
  endfunction
  always_comb begin
    out_sum = calculate_deep_sum(in_val);
  end
endmodule
module deep_ternary_module (
  input logic [0:150] select_bits,
  input logic [0:151] data_in,
  output logic out_data
);
  function automatic logic eval_deep_ternary(input logic [0:150] sel_in, input logic [0:151] data_in_local);
    return sel_in[0] ? data_in_local[0] :
           (sel_in[1] ? data_in_local[1] :
            (sel_in[2] ? data_in_local[2] :
             (sel_in[3] ? data_in_local[3] :
              (sel_in[4] ? data_in_local[4] :
               (sel_in[5] ? data_in_local[5] :
                (sel_in[6] ? data_in_local[6] :
                 (sel_in[7] ? data_in_local[7] :
                  (sel_in[8] ? data_in_local[8] :
                   (sel_in[9] ? data_in_local[9] :
                    (sel_in[10] ? data_in_local[10] :
                     (sel_in[11] ? data_in_local[11] :
                      (sel_in[12] ? data_in_local[12] :
                       (sel_in[13] ? data_in_local[13] :
                        (sel_in[14] ? data_in_local[14] :
                         (sel_in[15] ? data_in_local[15] :
                          (sel_in[16] ? data_in_local[16] :
                           (sel_in[17] ? data_in_local[17] :
                            (sel_in[18] ? data_in_local[18] :
                             (sel_in[19] ? data_in_local[19] :
                              (sel_in[20] ? data_in_local[20] :
                               (sel_in[21] ? data_in_local[21] :
                                (sel_in[22] ? data_in_local[22] :
                                 (sel_in[23] ? data_in_local[23] :
                                  (sel_in[24] ? data_in_local[24] :
                                   (sel_in[25] ? data_in_local[25] :
                                    (sel_in[26] ? data_in_local[26] :
                                     (sel_in[27] ? data_in_local[27] :
                                      (sel_in[28] ? data_in_local[28] :
                                       (sel_in[29] ? data_in_local[29] :
                                        (sel_in[30] ? data_in_local[30] :
                                         (sel_in[31] ? data_in_local[31] :
                                          (sel_in[32] ? data_in_local[32] :
                                           (sel_in[33] ? data_in_local[33] :
                                            (sel_in[34] ? data_in_local[34] :
                                             (sel_in[35] ? data_in_local[35] :
                                              (sel_in[36] ? data_in_local[36] :
                                               (sel_in[37] ? data_in_local[37] :
                                                (sel_in[38] ? data_in_local[38] :
                                                 (sel_in[39] ? data_in_local[39] :
                                                  (sel_in[40] ? data_in_local[40] :
                                                   (sel_in[41] ? data_in_local[41] :
                                                    (sel_in[42] ? data_in_local[42] :
                                                     (sel_in[43] ? data_in_local[43] :
                                                      (sel_in[44] ? data_in_local[44] :
                                                       (sel_in[45] ? data_in_local[45] :
                                                        (sel_in[46] ? data_in_local[46] :
                                                         (sel_in[47] ? data_in_local[47] :
                                                          (sel_in[48] ? data_in_local[48] :
                                                           (sel_in[49] ? data_in_local[49] :
                                                            (sel_in[50] ? data_in_local[50] :
                                                             (sel_in[51] ? data_in_local[51] :
                                                              (sel_in[52] ? data_in_local[52] :
                                                               (sel_in[53] ? data_in_local[53] :
                                                                (sel_in[54] ? data_in_local[54] :
                                                                 (sel_in[55] ? data_in_local[55] :
                                                                  (sel_in[56] ? data_in_local[56] :
                                                                   (sel_in[57] ? data_in_local[57] :
                                                                    (sel_in[58] ? data_in_local[58] :
                                                                     (sel_in[59] ? data_in_local[59] :
                                                                      (sel_in[60] ? data_in_local[60] :
                                                                       (sel_in[61] ? data_in_local[61] :
                                                                        (sel_in[62] ? data_in_local[62] :
                                                                         (sel_in[63] ? data_in_local[63] :
                                                                          (sel_in[64] ? data_in_local[64] :
                                                                           (sel_in[65] ? data_in_local[65] :
                                                                            (sel_in[66] ? data_in_local[66] :
                                                                             (sel_in[67] ? data_in_local[67] :
                                                                              (sel_in[68] ? data_in_local[68] :
                                                                               (sel_in[69] ? data_in_local[69] :
                                                                                (sel_in[70] ? data_in_local[70] :
                                                                                 (sel_in[71] ? data_in_local[71] :
                                                                                  (sel_in[72] ? data_in_local[72] :
                                                                                   (sel_in[73] ? data_in_local[73] :
                                                                                    (sel_in[74] ? data_in_local[74] :
                                                                                     (sel_in[75] ? data_in_local[75] :
                                                                                      (sel_in[76] ? data_in_local[76] :
                                                                                       (sel_in[77] ? data_in_local[77] :
                                                                                        (sel_in[78] ? data_in_local[78] :
                                                                                         (sel_in[79] ? data_in_local[79] :
                                                                                          (sel_in[80] ? data_in_local[80] :
                                                                                           (sel_in[81] ? data_in_local[81] :
                                                                                            (sel_in[82] ? data_in_local[82] :
                                                                                             (sel_in[83] ? data_in_local[83] :
                                                                                              (sel_in[84] ? data_in_local[84] :
                                                                                               (sel_in[85] ? data_in_local[85] :
                                                                                                (sel_in[86] ? data_in_local[86] :
                                                                                                 (sel_in[87] ? data_in_local[87] :
                                                                                                  (sel_in[88] ? data_in_local[88] :
                                                                                                   (sel_in[89] ? data_in_local[89] :
                                                                                                    (sel_in[90] ? data_in_local[90] :
                                                                                                     (sel_in[91] ? data_in_local[91] :
                                                                                                      (sel_in[92] ? data_in_local[92] :
                                                                                                       (sel_in[93] ? data_in_local[93] :
                                                                                                        (sel_in[94] ? data_in_local[94] :
                                                                                                         (sel_in[95] ? data_in_local[95] :
                                                                                                          (sel_in[96] ? data_in_local[96] :
                                                                                                           (sel_in[97] ? data_in_local[97] :
                                                                                                            (sel_in[98] ? data_in_local[98] :
                                                                                                             (sel_in[99] ? data_in_local[99] :
                                                                                                              (sel_in[100] ? data_in_local[100] :
                                                                                                               (sel_in[101] ? data_in_local[101] :
                                                                                                                (sel_in[102] ? data_in_local[102] :
                                                                                                                 (sel_in[103] ? data_in_local[103] :
                                                                                                                  (sel_in[104] ? data_in_local[104] :
                                                                                                                   (sel_in[105] ? data_in_local[105] :
                                                                                                                    (sel_in[106] ? data_in_local[106] :
                                                                                                                     (sel_in[107] ? data_in_local[107] :
                                                                                                                      (sel_in[108] ? data_in_local[108] :
                                                                                                                       (sel_in[109] ? data_in_local[109] :
                                                                                                                        (sel_in[110] ? data_in_local[110] :
                                                                                                                         (sel_in[111] ? data_in_local[111] :
                                                                                                                          (sel_in[112] ? data_in_local[112] :
                                                                                                                           (sel_in[113] ? data_in_local[113] :
                                                                                                                            (sel_in[114] ? data_in_local[114] :
                                                                                                                             (sel_in[115] ? data_in_local[115] :
                                                                                                                              (sel_in[116] ? data_in_local[116] :
                                                                                                                               (sel_in[117] ? data_in_local[117] :
                                                                                                                                (sel_in[118] ? data_in_local[118] :
                                                                                                                                 (sel_in[119] ? data_in_local[119] :
                                                                                                                                  (sel_in[120] ? data_in_local[120] :
                                                                                                                                   (sel_in[121] ? data_in_local[121] :
                                                                                                                                    (sel_in[122] ? data_in_local[122] :
                                                                                                                                     (sel_in[123] ? data_in_local[123] :
                                                                                                                                      (sel_in[124] ? data_in_local[124] :
                                                                                                                                       (sel_in[125] ? data_in_local[125] :
                                                                                                                                        (sel_in[126] ? data_in_local[126] :
                                                                                                                                         (sel_in[127] ? data_in_local[127] :
                                                                                                                                          (sel_in[128] ? data_in_local[128] :
                                                                                                                                           (sel_in[129] ? data_in_local[129] :
                                                                                                                                            (sel_in[130] ? data_in_local[130] :
                                                                                                                                             (sel_in[131] ? data_in_local[131] :
                                                                                                                                              (sel_in[132] ? data_in_local[132] :
                                                                                                                                               (sel_in[133] ? data_in_local[133] :
                                                                                                                                                (sel_in[134] ? data_in_local[134] :
                                                                                                                                                 (sel_in[135] ? data_in_local[135] :
                                                                                                                                                  (sel_in[136] ? data_in_local[136] :
                                                                                                                                                   (sel_in[137] ? data_in_local[137] :
                                                                                                                                                    (sel_in[138] ? data_in_local[138] :
                                                                                                                                                     (sel_in[139] ? data_in_local[139] :
                                                                                                                                                      (sel_in[140] ? data_in_local[140] :
                                                                                                                                                       (sel_in[141] ? data_in_local[141] :
                                                                                                                                                        (sel_in[142] ? data_in_local[142] :
                                                                                                                                                         (sel_in[143] ? data_in_local[143] :
                                                                                                                                                          (sel_in[144] ? data_in_local[144] :
                                                                                                                                                           (sel_in[145] ? data_in_local[145] :
                                                                                                                                                            (sel_in[146] ? data_in_local[146] :
                                                                                                                                                             (sel_in[147] ? data_in_local[147] :
                                                                                                                                                              (sel_in[148] ? data_in_local[148] :
                                                                                                                                                               (sel_in[149] ? data_in_local[149] :
                                                                                                                                                                (sel_in[150] ? data_in_local[150] : data_in_local[151]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         ;
  endfunction
  always_comb begin
    out_data = eval_deep_ternary(select_bits, data_in);
  end
endmodule
module task_func_module (
  input logic [7:0] in_a,
  input logic [7:0] in_b,
  input logic [7:0] in_e,
  output logic [7:0] out_c,
  output logic [7:0] out_d
);
  task automatic my_task (input logic [7:0] task_in1, input logic [7:0] task_in2, output logic [7:0] task_out);
    logic [7:0] temp_val;
    temp_val = task_in1 + task_in2 + 1; 
    task_out = temp_val;
  endtask
  function automatic logic [7:0] my_function (input logic [7:0] func_in1, input logic [7:0] func_in2);
    logic [7:0] result_val;
    result_val = func_in1 * func_in2 - 2; 
    return result_val;
  endfunction
  always_comb begin
    logic [7:0] task_result;
    logic [7:0] func_result;
    my_task(in_a, in_b, task_result);
    out_c = task_result;
    func_result = my_function(in_b, in_e);
    out_d = func_result;
  end
endmodule
module class_method_module (
  input int input_val,
  output int output_val
);
  class MyClass;
    int m_internal_data; 
    function new(int init_data);
      m_internal_data = init_data;
    endfunction
    function int get_scaled_data();
      return m_internal_data * 2;
    endfunction
    function void set_data(int new_data);
      m_internal_data = new_data; 
    endfunction
    static function int get_fixed_value();
      return 123;
    endfunction
  endclass : MyClass
  MyClass my_inst; 
  always_comb begin
    if (my_inst == null) begin
      my_inst = new(input_val); 
    end else begin
      my_inst.set_data(input_val + MyClass::get_fixed_value()); 
    end
    output_val = my_inst.get_scaled_data();
  end
endmodule
