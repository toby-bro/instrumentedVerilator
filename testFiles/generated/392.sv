module snippet (
    input wire clk,
    input logic [7:0] inj_denominator_1755007885622_558,
    input logic [15:0] inj_dividend_mod_1755007885622_216,
    input logic [7:0] inj_divisor_mod_1755007885622_714,
    input logic inj_nm_in_1755007885622_917,
    input logic [15:0] inj_numerator_1755007885622_262,
    input wire reset,
    output logic inj_nm_out_1755007885622_129,
    output logic [15:0] inj_quotient_1755007885622_622,
    output logic [7:0] inj_remainder_1755007885622_35
);
    // BEGIN: div_mod_ops_ts1755007885622
    // BEGIN: nested_module_ts1755007885622
    assign inj_nm_out_1755007885622_129 = inj_nm_in_1755007885622_917;
    // END: nested_module_ts1755007885622

    assign inj_quotient_1755007885622_622 = (inj_denominator_1755007885622_558 == 0) ? 16'hFFFF : (inj_numerator_1755007885622_262 / inj_denominator_1755007885622_558); 
    assign inj_remainder_1755007885622_35 = (inj_divisor_mod_1755007885622_714 == 0) ? 8'hFF : (inj_dividend_mod_1755007885622_216 % inj_divisor_mod_1755007885622_714);
    // END: div_mod_ops_ts1755007885622
endmodule

