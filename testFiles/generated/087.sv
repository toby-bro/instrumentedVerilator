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

module ImplicitTimeScaleModule (
    input logic in_its,
    output logic out_its
);
    assign out_its = in_its;
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

module mod_case_standard (
    input bit [7:0] in_cmd,
    output bit [3:0] out_status
);
always_comb begin
    case (in_cmd)
        8'd0, 8'd1, 8'd2: begin
            out_status = 4'hA;
        end
        8'd3, 8'd4: begin
            out_status = 4'hB;
        end
        default: begin
            out_status = 4'hF;
        end
    endcase
end
endmodule

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module snippet (
    input wire clk,
    input logic inj_a_1755007781308_769,
    input logic inj_b_1755007781308_725,
    input bit [7:0] inj_in_cmd_1755007781308_766,
    input logic [38:0] inj_in_packed_for_conv_1755007781308_877,
    input logic [7:0] inj_in_vec_1755007781308_929,
    input wire [31:0] inj_wide_in_1755007781308_101,
    input wire reset,
    output wire [7:0] inj_lower_byte_out_1755007781308_843,
    output logic inj_out_bit_conv_1755007781308_676,
    output int inj_out_int_conv_1755007781308_370,
    output logic inj_out_its_1755007781309_544,
    output bit [3:0] inj_out_status_1755007781308_887,
    output logic [7:0] inj_out_unpacked_struct_repacked_1755007781308_153,
    output logic [5:0] inj_out_vec_conv_1755007781308_385,
    output logic inj_sum_1755007781308_263,
    output wire [7:0] inj_upper_byte_out_1755007781308_153
);
    // BEGIN: part_select_ops_ts1755007781308
    wire [31:0] processed_wide_ts1755007781308;
        ImplicitTimeScaleModule ImplicitTimeScaleModule_inst_1755007781309_5409 (
            .in_its(inj_b_1755007781308_725),
            .out_its(inj_out_its_1755007781309_544)
        );
        mod_case_standard mod_case_standard_inst_1755007781308_4784 (
            .out_status(inj_out_status_1755007781308_887),
            .in_cmd(inj_in_cmd_1755007781308_766)
        );
    assign processed_wide_ts1755007781308 = inj_wide_in_1755007781308_101 * 2;
    assign inj_upper_byte_out_1755007781308_153 = processed_wide_ts1755007781308[31:24];
    assign inj_lower_byte_out_1755007781308_843 = processed_wide_ts1755007781308[7:0];
    // END: part_select_ops_ts1755007781308

    simple_adder simple_adder_inst_1755007781308_2393 (
        .a(inj_a_1755007781308_769),
        .b(inj_b_1755007781308_725),
        .sum(inj_sum_1755007781308_263)
    );
    assign_pattern_lvalue assign_pattern_lvalue_inst_1755007781308_3228 (
        .out_unpacked_struct_repacked(inj_out_unpacked_struct_repacked_1755007781308_153),
        .out_vec_conv(inj_out_vec_conv_1755007781308_385),
        .in_packed_for_conv(inj_in_packed_for_conv_1755007781308_877),
        .in_vec(inj_in_vec_1755007781308_929),
        .out_bit_conv(inj_out_bit_conv_1755007781308_676),
        .out_int_conv(inj_out_int_conv_1755007781308_370)
    );
endmodule

