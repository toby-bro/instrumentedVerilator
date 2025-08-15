module ModScalarsArrays (
    input logic in_scalar,
    output logic out_scalar
);
    parameter int P_INT = 10;
    localparam byte LP_BYTE = 8'hFF;
    const logic C_BOOL = 1'b1;
    localparam logic [63:0] LP_WIDE = 64'hFEEDFACE_CAFEBEEF;
    const logic [127:0] VERY_WIDE_CONST = 128'h0123456789ABCDEF0123456789ABCDEF;
    parameter string P_STRING = "Hello Verilator Const Pool! This is a long string.";
    localparam real LP_REAL = 3.14159265;
    const real C_SHORTREAL = 1.23e-5;
    parameter logic [7:0] PACKED_ARRAY_P [0:2] = '{8'h11, 8'h22, 8'h33};
    parameter int UNPACKED_ARRAY_P [1:2][3:4] = '{{10, 20}, {30, 40}};
    localparam int EXPR_CONST = P_INT * 2 + LP_BYTE;
    assign out_scalar = in_scalar && C_BOOL && (LP_WIDE[0] == 1'b1) && (EXPR_CONST > 0);
endmodule
module ModEnumsStructsUnions (
    input byte in_byte,
    output int out_int
);
    typedef enum { IDLE, RUNNING, STOPPED, ERROR_STATE } FsmState;
    parameter FsmState DEFAULT_STATE = IDLE;
    localparam FsmState CURRENT_STATE = RUNNING;
    typedef struct packed {
        logic [3:0] field_a;
        logic [3:0] field_b;
        int         field_c;
    } SmallStruct_t;
    parameter SmallStruct_t MY_STRUCT_P = '{field_a: 4'hA, field_b: 4'hB, field_c: 100};
    typedef union packed {
        logic [63:0] val_int_bits;
        logic [63:0] val_real_bits;
        logic [63:0] val_logic_bits;
    } DataUnion_t;
    parameter DataUnion_t MY_UNION_P = '{val_int_bits: 64'd12345};
    localparam DataUnion_t MY_UNION_P_REAL = '{val_real_bits: $realtobits(6.78)};
    assign out_int = in_byte + int'(DEFAULT_STATE) + MY_STRUCT_P.field_a +
                     int'(MY_UNION_P.val_int_bits) + MY_STRUCT_P.field_c +
                     int'($bits(MY_UNION_P_REAL.val_real_bits) ? $bitstoreal(MY_UNION_P_REAL.val_real_bits) * 10 : 0);
endmodule
module ModClassConstants (
    input longint in_long,
    output int out_val
);
    class ConfigData;
        static const int MAX_VALUE = 1000;
        static const string VERSION_STR = "v1.2.3 Verilator build-info";
        static const logic [31:0] MAGIC_NUMBER = 32'hDEADBEEF;
        static const real PI_VAL = 3.14159;
    endclass
    class LocalTempClass;
        const int LOCAL_ID;
        function new(int id);
            this.LOCAL_ID = id;
        endfunction
    endclass
    function automatic int get_dummy_instance_value(int seed);
        LocalTempClass local_obj = new(seed);
        return local_obj.LOCAL_ID;
    endfunction
    int local_out_val;
    always_comb begin
        local_out_val = ConfigData::MAX_VALUE;
        if (in_long > 0) begin
            local_out_val = local_out_val + ConfigData::VERSION_STR.len() + ConfigData::MAGIC_NUMBER[0] + int'(ConfigData::PI_VAL * 10);
        end else begin
            local_out_val = local_out_val + ConfigData::MAGIC_NUMBER[31];
        end
        local_out_val = local_out_val + get_dummy_instance_value(int'(in_long % 10));
    end
    assign out_val = local_out_val;
endmodule
module ModManyConstants (
    input bit in_bit,
    output int out_sum
);
    localparam int C0 = 0;
    localparam int C1 = 1;
    localparam int C2 = 2;
    localparam int C3 = 3;
    localparam int C4 = 4;
    localparam int C5 = 5;
    localparam int C6 = 6;
    localparam int C7 = 7;
    localparam int C8 = 8;
    localparam int C9 = 9;
    localparam int C10 = 10;
    localparam int C11 = 11;
    localparam int C12 = 12;
    localparam int C13 = 13;
    localparam int C14 = 14;
    localparam int C15 = 15;
    localparam int C16 = 16;
    localparam int C17 = 17;
    localparam int C18 = 18;
    localparam int C19 = 19;
    localparam int C20 = 20;
    localparam int C21 = 21;
    localparam int C22 = 22;
    localparam int C23 = 23;
    localparam int C24 = 24;
    localparam int C25 = 25;
    localparam int C26 = 26;
    localparam int C27 = 27;
    localparam int C28 = 28;
    localparam int C29 = 29;
    localparam int C30 = 30;
    localparam int C31 = 31;
    localparam int C32 = 32;
    localparam int C33 = 33;
    localparam int C34 = 34;
    localparam int C35 = 35;
    localparam int C36 = 36;
    localparam int C37 = 37;
    localparam int C38 = 38;
    localparam int C39 = 39;
    localparam int C40 = 40;
    localparam int C41 = 41;
    localparam int C42 = 42;
    localparam int C43 = 43;
    localparam int C44 = 44;
    localparam int C45 = 45;
    localparam int C46 = 46;
    localparam int C47 = 47;
    localparam int C48 = 48;
    localparam int C49 = 49;
    localparam int C50 = 50;
    localparam int C51 = 51;
    localparam int C52 = 52;
    localparam int C53 = 53;
    localparam int C54 = 54;
    localparam int C55 = 55;
    localparam int C56 = 56;
    localparam int C57 = 57;
    localparam int C58 = 58;
    localparam int C59 = 59;
    localparam int C60 = 60;
    localparam int C61 = 61;
    localparam int C62 = 62;
    localparam int C63 = 63;
    localparam int C64 = 64;
    localparam int C65 = 65;
    localparam int C66 = 66;
    localparam int C67 = 67;
    localparam int C68 = 68;
    localparam int C69 = 69;
    localparam int C70 = 70;
    localparam int C71 = 71;
    localparam int C72 = 72;
    localparam int C73 = 73;
    localparam int C74 = 74;
    localparam int C75 = 75;
    localparam int C76 = 76;
    localparam int C77 = 77;
    localparam int C78 = 78;
    localparam int C79 = 79;
    localparam int C80 = 80;
    localparam int C81 = 81;
    localparam int C82 = 82;
    localparam int C83 = 83;
    localparam int C84 = 84;
    localparam int C85 = 85;
    localparam int C86 = 86;
    localparam int C87 = 87;
    localparam int C88 = 88;
    localparam int C89 = 89;
    localparam int C90 = 90;
    localparam int C91 = 91;
    localparam int C92 = 92;
    localparam int C93 = 93;
    localparam int C94 = 94;
    localparam int C95 = 95;
    localparam int C96 = 96;
    localparam int C97 = 97;
    localparam int C98 = 98;
    localparam int C99 = 99;
    assign out_sum = C0 + C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8 + C9 +
                     C10 + C11 + C12 + C13 + C14 + C15 + C16 + C17 + C18 + C19 +
                     C20 + C21 + C22 + C23 + C24 + C25 + C26 + C27 + C28 + C29 +
                     C30 + C31 + C32 + C33 + C34 + C35 + C36 + C37 + C38 + C39 +
                     C40 + C41 + C42 + C43 + C44 + C45 + C46 + C47 + C48 + C49 +
                     C50 + C51 + C52 + C53 + C54 + C55 + C56 + C57 + C58 + C59 +
                     C60 + C61 + C62 + C63 + C64 + C65 + C66 + C67 + C68 + C69 +
                     C70 + C71 + C72 + C73 + C74 + C75 + C76 + C77 + C78 + C79 +
                     C80 + C81 + C82 + C83 + C84 + C85 + C86 + C87 + C88 + C89 +
                     C90 + C91 + C92 + C93 + C94 + C95 + C96 + C97 + C98 + C99 + int'(in_bit);
endmodule
