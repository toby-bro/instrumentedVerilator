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

module snippet (
    input wire clk,
    input logic [38:0] inj_in_packed_for_conv_1755007914002_138,
    input logic [7:0] inj_in_vec_1755007914002_834,
    input wire reset,
    output logic inj_out_bit_conv_1755007914002_614,
    output int inj_out_int_conv_1755007914002_23,
    output logic [7:0] inj_out_unpacked_struct_repacked_1755007914002_218,
    output logic [5:0] inj_out_vec_conv_1755007914002_259
);
    // BEGIN: assign_pattern_lvalue_ts1755007914002
    eight_bit_unpacked_struct_t unpacked_s;
    logic [7:0] reg_unpacked_struct_repacked_ts1755007914002;
    int int_var_ts1755007914002;
    logic bit_var_ts1755007914002;
    logic [5:0] vec_var_ts1755007914002;
    always_comb begin
        unpacked_s.f1 = inj_in_vec_1755007914002_834[3:0];
        unpacked_s.f2 = inj_in_vec_1755007914002_834[4];
        unpacked_s.f3 = inj_in_vec_1755007914002_834[7:5];
        reg_unpacked_struct_repacked_ts1755007914002 = { unpacked_s.f3, unpacked_s.f2, unpacked_s.f1 };
        int_var_ts1755007914002 = inj_in_packed_for_conv_1755007914002_138[31:0];
        bit_var_ts1755007914002 = inj_in_packed_for_conv_1755007914002_138[32];
        vec_var_ts1755007914002 = inj_in_packed_for_conv_1755007914002_138[38:33];
        inj_out_unpacked_struct_repacked_1755007914002_218 = reg_unpacked_struct_repacked_ts1755007914002;
        inj_out_int_conv_1755007914002_23 = int_var_ts1755007914002;
        inj_out_bit_conv_1755007914002_614 = bit_var_ts1755007914002;
        inj_out_vec_conv_1755007914002_259 = vec_var_ts1755007914002;
    end
    // END: assign_pattern_lvalue_ts1755007914002
endmodule

