typedef struct packed {
    logic [3:0] f1;
    logic       f2;
    logic [2:0] f3;
} eight_bit_unpacked_struct_t;
typedef struct packed {
    logic [3:0] f1;
    logic f2;
    logic [2:0] f3;
} eight_bit_unpacked_struct_t;

module PragmaProtectBoundaries (
    input logic start_protect,
    output logic protected_active
);
logic internal_state;
`ifdef SLANG_PRAGMA
`protect begin
`endif
assign internal_state = start_protect;
`ifdef SLANG_PRAGMA
`protect end
`endif
`ifdef SLANG_PRAGMA
`protect begin_protected
`endif
`ifdef SLANG_PRAGMA
`protect end_protected
`endif
assign protected_active = internal_state;
endmodule

module assign_pattern_lvalue (
    input logic [38:0] in_packed_for_conv,
    input logic [7:0] in_vec,
    output logic out_bit_conv,
    output int out_int_conv,
    output logic [7:0] out_unpacked_struct_repacked,
    output logic [5:0] out_vec_conv
);
    eight_bit_unpacked_struct_t unpacked_s;
    logic [7:0] reg_unpacked_struct_repacked;
    int int_var;
    logic bit_var;
    logic [5:0] vec_var;
    always_comb begin
        unpacked_s.f1 = in_vec[3:0];
        unpacked_s.f2 = in_vec[4];
        unpacked_s.f3 = in_vec[7:5];
        reg_unpacked_struct_repacked = { unpacked_s.f3, unpacked_s.f2, unpacked_s.f1 };
        int_var = in_packed_for_conv[31:0];
        bit_var = in_packed_for_conv[32];
        vec_var = in_packed_for_conv[38:33];
        out_unpacked_struct_repacked = reg_unpacked_struct_repacked;
        out_int_conv = int_var;
        out_bit_conv = bit_var;
        out_vec_conv = vec_var;
    end
endmodule

module snippet (
    input wire clk,
    input logic [38:0] inj_in_packed_for_conv_1755007876850_814,
    input logic [7:0] inj_in_vec_1755007876850_450,
    input logic inj_start_protect_1755007876850_809,
    input wire reset,
    output logic inj_out_bit_conv_1755007876850_861,
    output int inj_out_int_conv_1755007876850_239,
    output logic [7:0] inj_out_unpacked_struct_repacked_1755007876850_136,
    output logic [5:0] inj_out_vec_conv_1755007876850_413,
    output logic inj_protected_active_1755007876850_674
);
    PragmaProtectBoundaries PragmaProtectBoundaries_inst_1755007876850_8195 (
        .start_protect(inj_start_protect_1755007876850_809),
        .protected_active(inj_protected_active_1755007876850_674)
    );
    assign_pattern_lvalue assign_pattern_lvalue_inst_1755007876850_8906 (
        .out_int_conv(inj_out_int_conv_1755007876850_239),
        .out_unpacked_struct_repacked(inj_out_unpacked_struct_repacked_1755007876850_136),
        .out_vec_conv(inj_out_vec_conv_1755007876850_413),
        .in_packed_for_conv(inj_in_packed_for_conv_1755007876850_814),
        .in_vec(inj_in_vec_1755007876850_450),
        .out_bit_conv(inj_out_bit_conv_1755007876850_861)
    );
endmodule

