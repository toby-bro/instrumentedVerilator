module snippet (
    input wire clk,
    input logic [7:0] inj_denominator_1755007780535_117,
    input logic [15:0] inj_dividend_mod_1755007780535_892,
    input logic [7:0] inj_divisor_mod_1755007780535_140,
    input wire [1:0] inj_i_sel_1755007780533_831,
    input wire [3:0] inj_i_val_1755007780533_418,
    input logic [15:0] inj_numerator_1755007780535_137,
    input wire reset,
    output logic [3:0] inj_o_out_1755007780533_838,
    output logic [15:0] inj_quotient_1755007780535_24,
    output logic [7:0] inj_remainder_1755007780535_960
);
    // BEGIN: mod_case_block_attrs_ts1755007780534
    logic [3:0] l_temp_ts1755007780534;
        // BEGIN: div_mod_ops_ts1755007780535
        assign inj_quotient_1755007780535_24 = (inj_denominator_1755007780535_117 == 0) ? 16'hFFFF : (inj_numerator_1755007780535_137 / inj_denominator_1755007780535_117); 
        assign inj_remainder_1755007780535_960 = (inj_divisor_mod_1755007780535_140 == 0) ? 8'hFF : (inj_dividend_mod_1755007780535_892 % inj_divisor_mod_1755007780535_140);
        // END: div_mod_ops_ts1755007780535

    always_comb begin
        (* full_case *)
        (* parallel_case *)
        case (inj_i_sel_1755007780533_831)
            2'b00: l_temp_ts1755007780534 = inj_i_val_1755007780533_418;
            2'b01: l_temp_ts1755007780534 = inj_i_val_1755007780533_418 << 1;
            2'b10: l_temp_ts1755007780534 = inj_i_val_1755007780533_418 >> 1;
            default: l_temp_ts1755007780534 = 4'bxxxx;
        endcase
        (* coverage_off *)
        begin : my_named_block
            inj_o_out_1755007780533_838 = l_temp_ts1755007780534;
        end
    end
    // END: mod_case_block_attrs_ts1755007780534
endmodule

