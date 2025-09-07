module snippet (
    input wire clk,
    input wire [1:0] inj_i_sel_1755007772864_286,
    input wire [3:0] inj_i_val_1755007772864_826,
    input logic [2:0] inj_mode_1755007772865_758,
    input logic [7:0] inj_val1_1755007772865_954,
    input logic [7:0] inj_val2_1755007772865_470,
    input wire reset,
    output logic [3:0] inj_o_out_1755007772864_740,
    output logic [7:0] inj_res_1755007772865_379
);
    // BEGIN: mod_case_block_attrs_ts1755007772864
    logic [3:0] l_temp_ts1755007772864;
        // BEGIN: dup_nested_if_ts1755007772866
        always_comb begin
            inj_res_1755007772865_379 = '0;
            if (inj_mode_1755007772865_758 == 3'b001) begin
                if (inj_val1_1755007772865_954 > inj_val2_1755007772865_470) begin
                    inj_res_1755007772865_379 = inj_val1_1755007772865_954 + inj_val2_1755007772865_470;
                end else begin
                    inj_res_1755007772865_379 = inj_val1_1755007772865_954 - inj_val2_1755007772865_470;
                end
            end else if (inj_mode_1755007772865_758 == 3'b010) begin
                if (inj_val1_1755007772865_954 > inj_val2_1755007772865_470) begin
                    inj_res_1755007772865_379 = inj_val1_1755007772865_954 + inj_val2_1755007772865_470;
                end else begin
                    inj_res_1755007772865_379 = inj_val1_1755007772865_954 - inj_val2_1755007772865_470;
                end
            end else if (inj_mode_1755007772865_758 == 3'b011) begin
                if (inj_val1_1755007772865_954 < inj_val2_1755007772865_470) begin
                    inj_res_1755007772865_379 = inj_val1_1755007772865_954 * inj_val2_1755007772865_470;
                end else begin
                    inj_res_1755007772865_379 = inj_val1_1755007772865_954 / ((inj_val2_1755007772865_470 == 0) ? 1 : inj_val2_1755007772865_470);
                end
            end else if (inj_mode_1755007772865_758 == 3'b100) begin
                if (inj_val1_1755007772865_954 != inj_val2_1755007772865_470) begin
                    if (inj_val1_1755007772865_954 > inj_val2_1755007772865_470) inj_res_1755007772865_379 = inj_val1_1755007772865_954;
                    else inj_res_1755007772865_379 = inj_val2_1755007772865_470;
                end else begin
                    inj_res_1755007772865_379 = inj_val1_1755007772865_954 + inj_val2_1755007772865_470;
                end
            end
            else begin
                inj_res_1755007772865_379 = inj_val1_1755007772865_954 ^ inj_val2_1755007772865_470;
            end
        end
        // END: dup_nested_if_ts1755007772866

    always_comb begin
        (* full_case *)
        (* parallel_case *)
        case (inj_i_sel_1755007772864_286)
            2'b00: l_temp_ts1755007772864 = inj_i_val_1755007772864_826;
            2'b01: l_temp_ts1755007772864 = inj_i_val_1755007772864_826 << 1;
            2'b10: l_temp_ts1755007772864 = inj_i_val_1755007772864_826 >> 1;
            default: l_temp_ts1755007772864 = 4'bxxxx;
        endcase
        (* coverage_off *)
        begin : my_named_block
            inj_o_out_1755007772864_740 = l_temp_ts1755007772864;
        end
    end
    // END: mod_case_block_attrs_ts1755007772864
endmodule

