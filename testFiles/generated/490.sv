module snippet (
    input wire clk,
    input wire [31:0] inj_data_in_1755007918146_967,
    input logic [15:0] inj_dividend_mod_1755007918149_870,
    input logic [7:0] inj_divisor_mod_1755007918149_722,
    input logic inj_i_in_1755007918150_738,
    input wire [3:0] inj_i_val_1755007918147_2,
    input wire [1:0] inj_in_const_index_1755007918147_755,
    input wire [7:0] inj_in_data_1755007918147_765,
    input wire [1:0] inj_in_index_1755007918147_570,
    input logic [15:0] inj_numerator_1755007918149_831,
    input wire reset,
    output logic [31:0] inj_data_out_1755007918146_705,
    output logic [3:0] inj_o_out_1755007918147_574,
    output logic inj_o_out_1755007918150_582,
    output logic [7:0] inj_out_array_sel_const_1755007918147_311,
    output logic [7:0] inj_out_array_sel_var_1755007918147_894,
    output logic [15:0] inj_quotient_1755007918149_402,
    output logic [7:0] inj_remainder_1755007918149_316
);
    // BEGIN: mod_part_select_ts1755007918146
    logic [31:0] temp_reg_ts1755007918146;
        // BEGIN: Mod_ArrayOps_ts1755007918147
        logic [7:0] my_array_ts1755007918147 [3:0];
            // BEGIN: mod_case_block_attrs_ts1755007918148
            logic [3:0] l_temp_ts1755007918148;
                // BEGIN: extern_declarations_ts1755007918150
                assign inj_o_out_1755007918150_582 = inj_i_in_1755007918150_738;
                // END: extern_declarations_ts1755007918150

                // BEGIN: div_mod_ops_ts1755007918149
                assign inj_quotient_1755007918149_402 = (my_array_ts1755007918147 == 0) ? 16'hFFFF : (inj_numerator_1755007918149_831 / my_array_ts1755007918147); 
                assign inj_remainder_1755007918149_316 = (inj_divisor_mod_1755007918149_722 == 0) ? 8'hFF : (inj_dividend_mod_1755007918149_870 % inj_divisor_mod_1755007918149_722);
                // END: div_mod_ops_ts1755007918149

            always_comb begin
                (* full_case *)
                (* parallel_case *)
                case (inj_in_const_index_1755007918147_755)
                    2'b00: l_temp_ts1755007918148 = inj_i_val_1755007918147_2;
                    2'b01: l_temp_ts1755007918148 = inj_i_val_1755007918147_2 << 1;
                    2'b10: l_temp_ts1755007918148 = inj_i_val_1755007918147_2 >> 1;
                    default: l_temp_ts1755007918148 = 4'bxxxx;
                endcase
                (* coverage_off *)
                begin : my_named_block
                    inj_o_out_1755007918147_574 = l_temp_ts1755007918148;
                end
            end
            // END: mod_case_block_attrs_ts1755007918148

        always_comb begin
            my_array_ts1755007918147[0] = inj_in_data_1755007918147_765;
            my_array_ts1755007918147[1] = inj_in_data_1755007918147_765 + 8'd1;
            my_array_ts1755007918147[2] = inj_in_data_1755007918147_765 + 8'd2;
            my_array_ts1755007918147[3] = inj_in_data_1755007918147_765 + 8'd3;
            inj_out_array_sel_var_1755007918147_894 = my_array_ts1755007918147[inj_in_index_1755007918147_570];
            inj_out_array_sel_const_1755007918147_311 = my_array_ts1755007918147[inj_in_const_index_1755007918147_755];
        end
        // END: Mod_ArrayOps_ts1755007918147

    always_comb begin
        temp_reg_ts1755007918146[7:0] = inj_data_in_1755007918146_967[7:0];
        temp_reg_ts1755007918146[15:8] = inj_data_in_1755007918146_967[23:16];
        temp_reg_ts1755007918146[31:16] = inj_data_in_1755007918146_967[15:0];
        temp_reg_ts1755007918146[0] = inj_data_in_1755007918146_967[31];
        temp_reg_ts1755007918146[8] = inj_data_in_1755007918146_967[0];
        inj_data_out_1755007918146_705 = temp_reg_ts1755007918146;
    end
    // END: mod_part_select_ts1755007918146
endmodule

