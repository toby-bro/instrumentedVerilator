module ConstModule_BasicAndWide (
    input logic [7:0] in_data_a,
    output logic [15:0] out_result_a
);
    parameter P_INT_DEC = 12345;
    parameter P_INT_HEX = 32'hABCD_EF01;
    parameter P_INT_BIN = 8'b1010_1010;
    parameter P_INT_SIGNED = -5678;
    parameter P_WIDE_128 = 128'hFEDC_BA98_7654_3210_FEDC_BA98_7654_3210;
    parameter P_VERY_WIDE_256 = 256'h1234_5678_9ABC_DEF0_1234_5678_9ABC_DEF0_1234_5678_9ABC_DEF0_1234_5678_9ABC_DEF0;
    parameter P_REAL = 3.1415926535;
    parameter P_STRING = "Verilator Constant Pool Test String";
    parameter P_STRING_EMPTY = "";
    parameter P_STRING_LONG = "This is a very long string that should contribute a significant amount to the m_outFileSize counter, potentially triggering file splitting logic if the options are configured appropriately for large constant pools and many constant declarations.";
    parameter P_EXPR_ADD = P_INT_DEC + 1000;
    parameter P_EXPR_MUL = P_INT_BIN * 5;
    parameter P_EXPR_SHIFT = P_INT_HEX >> 4;
    parameter P_EXPR_CONCAT_SIMPLE = {P_INT_BIN, 4'b0000};
    assign out_result_a = in_data_a + P_INT_DEC[15:0];
    localparam LP_MY_LOCAL = P_INT_DEC * 2;
    localparam LP_LOCAL_STRING = "Local string constant";
endmodule
module ConstModule_Arrays (
    input logic [15:0] in_addr_b,
    output logic [7:0] out_value_b
);
    parameter logic [31:0] P_PACKED_WORD = 32'hCAFE_BABE;
    parameter logic [7:0] P_PACKED_BYTE_ARRAY = {8'hAA, 8'hBB, 8'hCC, 8'hDD}; 
    parameter logic [7:0] P_UNPACKED_ARRAY_1D [3] = '{8'h10, 8'h20, 8'h30};
    parameter int P_UNPACKED_ARRAY_MULTI_DIM [2][2] = '{'{1, 2}, '{3, 4}};
    parameter string P_UNPACKED_STRING_ARRAY [2] = '{"First String Entry", "Second String Entry with More Chars"}; 
    parameter logic [63:0] P_UNPACKED_WIDE_ARRAY [2] = '{64'hAAAA_BBBB_CCCC_DDDD, 64'hEEEE_FFFF_1111_2222};
    parameter int P_UNPACKED_DEFAULT_ARRAY [2] = '{10, default: 99};
    assign out_value_b = P_UNPACKED_ARRAY_1D[in_addr_b % 3];
endmodule
module ConstModule_EnumsStructs (
    input logic in_select_c,
    output logic [15:0] out_output_c
);
    typedef enum bit [1:0] {
        IDLE = 2'b00,
        STATE_A = 2'b01,
        STATE_B = 2'b10,
        DONE = 2'b11
    } FSM_STATE_T;
    parameter FSM_STATE_T P_INITIAL_STATE = IDLE;
    parameter FSM_STATE_T P_FINAL_STATE = DONE;
    typedef struct packed {
        logic [7:0] field1;
        int         field2;
        bit         valid;
    } MyPackedData_t;
    parameter MyPackedData_t P_PACKED_DATA = '{field1: 8'hAB, field2: 100, valid: 1'b1};
    typedef struct {
        string      name;
        real        value;
        logic [3:0] id;
    } MyUnpackedInfo_t;
    parameter MyUnpackedInfo_t P_UNPACKED_INFO = '{name: "Info Constant Struct", value: 9.87, id: 4'hF};
    parameter MyPackedData_t P_PACKED_DATA_ARRAY [2] = '{
        '{field1: 8'h11, field2: 11, valid: 1'b0},
        '{field1: 8'h22, field2: 22, valid: 1'b1}
    };
    parameter FSM_STATE_T P_STATE_SEQUENCE [3] = '{IDLE, STATE_A, STATE_B};
    assign out_output_c = in_select_c ? P_PACKED_DATA.field2 : P_PACKED_DATA_ARRAY[0].field2;
endmodule
module ConstModule_ComplexExpressions (
    input logic [7:0] in_op_d,
    output logic [31:0] out_result_d
);
    localparam LP_BITWISE_AND = 32'hDEAD_BEEF & 32'hFFFF_0000;
    localparam LP_BITWISE_OR  = 32'h1111_2222 | 32'h0000_FFFF;
    localparam LP_BITWISE_XOR = 32'h1234_5678 ^ 32'h8765_4321;
    localparam LP_BITWISE_NOT = ~32'hF0F0_F0F0;
    localparam LP_ARITH_COMPLEX = (100 * 20) + (500 / 5) - (123 % 10);
    localparam LP_POWER = 2**10; 
    localparam LP_CONCAT_REPLICATE = { {2{4'b1010}}, {3{2'b11}} }; 
    localparam LP_SELECT_BITS = LP_CONCAT_REPLICATE[15:8];
    localparam LP_TERNARY = (LP_ARITH_COMPLEX > 1000) ? LP_BITWISE_AND : LP_BITWISE_OR;
    localparam LP_A0 = 1; localparam LP_A1 = 2; localparam LP_A2 = 3; localparam LP_A3 = 4; localparam LP_A4 = 5;
    localparam LP_A5 = 6; localparam LP_A6 = 7; localparam LP_A7 = 8; localparam LP_A8 = 9; localparam LP_A9 = 10;
    localparam LP_B0 = 11; localparam LP_B1 = 12; localparam LP_B2 = 13; localparam LP_B3 = 14; localparam LP_B4 = 15;
    localparam LP_B5 = 16; localparam LP_B6 = 17; localparam LP_B7 = 18; localparam LP_B8 = 19; localparam LP_B9 = 20;
    localparam LP_C0 = 21; localparam LP_C1 = 22; localparam LP_C2 = 23; localparam LP_C3 = 24; localparam LP_C4 = 25;
    localparam LP_C5 = 26; localparam LP_C6 = 27; localparam LP_C7 = 28; localparam LP_C8 = 29; localparam LP_C9 = 30;
    localparam LP_D0 = 31; localparam LP_D1 = 32; localparam LP_D2 = 33; localparam LP_D3 = 34; localparam LP_D4 = 35;
    localparam LP_D5 = 36; localparam LP_D6 = 37; localparam LP_D7 = 38; localparam LP_D8 = 39; localparam LP_D9 = 40;
    localparam LP_E0 = 41; localparam LP_E1 = 42; localparam LP_E2 = 43; localparam LP_E3 = 44; localparam LP_E4 = 45;
    localparam LP_E5 = 46; localparam LP_E6 = 47; localparam LP_E7 = 48; localparam LP_E8 = 49; localparam LP_E9 = 50;
    localparam LP_F0 = 51; localparam LP_F1 = 52; localparam LP_F2 = 53; localparam LP_F3 = 54; localparam LP_F4 = 55;
    localparam LP_F5 = 56; localparam LP_F6 = 57; localparam LP_F7 = 58; localparam LP_F8 = 59; localparam LP_F9 = 60;
    localparam LP_G0 = 61; localparam LP_G1 = 62; localparam LP_G2 = 63; localparam LP_G3 = 64; localparam LP_G4 = 65;
    localparam LP_G5 = 66; localparam LP_G6 = 67; localparam LP_G7 = 68; localparam LP_G8 = 69; localparam LP_G9 = 70;
    assign out_result_d = LP_TERNARY + in_op_d;
endmodule
module ConstModule_MixedTypes (
    input logic [3:0] in_idx_e,
    output logic [63:0] out_complex_e
);
    typedef struct packed {
        logic [7:0] reg_a;
        logic [7:0] reg_b;
    } RegPair_t;
    typedef struct {
        string      block_name;
        RegPair_t   registers[2]; 
        int         version;
    } BlockConfig_t;
    parameter BlockConfig_t P_BLOCK_CONFIG = '{
        block_name: "CPU_Block_Config_Type",
        registers: '{ '{reg_a: 8'hAA, reg_b: 8'hBB}, '{reg_a: 8'hCC, reg_b: 8'hDD} },
        version: 10
    };
    typedef enum bit [1:0] { LOW_PRI = 0, MED_PRI = 1, HIGH_PRI = 2 } Priority_e;
    parameter Priority_e P_PRIORITY_LIST [4] = '{MED_PRI, HIGH_PRI, LOW_PRI, MED_PRI};
    parameter logic [7:0] P_LARGE_DATA_TABLE [16] = '{
        8'h00, 8'h11, 8'h22, 8'h33, 8'h44, 8'h55, 8'h66, 8'h77,
        8'h88, 8'h99, 8'hAA, 8'hBB, 8'hCC, 8'hDD, 8'hEE, 8'hFF
    }; 
    assign out_complex_e = {P_BLOCK_CONFIG.version[15:0], P_BLOCK_CONFIG.registers[in_idx_e % 2].reg_a, P_LARGE_DATA_TABLE[in_idx_e]};
endmodule
