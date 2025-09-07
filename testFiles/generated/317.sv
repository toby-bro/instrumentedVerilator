module dup_nested_if (
    input logic [2:0] mode,
    input logic [7:0] val1,
    input logic [7:0] val2,
    output logic [7:0] res
);
    always_comb begin
        res = '0;
        if (mode == 3'b001) begin
            if (val1 > val2) begin
                res = val1 + val2;
            end else begin
                res = val1 - val2;
            end
        end else if (mode == 3'b010) begin
            if (val1 > val2) begin
                res = val1 + val2;
            end else begin
                res = val1 - val2;
            end
        end else if (mode == 3'b011) begin
            if (val1 < val2) begin
                res = val1 * val2;
            end else begin
                res = val1 / ((val2 == 0) ? 1 : val2);
            end
        end else if (mode == 3'b100) begin
            if (val1 != val2) begin
                if (val1 > val2) res = val1;
                else res = val2;
            end else begin
                res = val1 + val2;
            end
        end
        else begin
            res = val1 ^ val2;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_a_1755007861031_633,
    input logic inj_b_1755007861031_879,
    input logic [2:0] inj_mode_1755007861032_625,
    input logic [7:0] inj_val1_1755007861032_103,
    input logic [7:0] inj_val2_1755007861032_202,
    input wire reset,
    output logic inj_out_a_1755007861031_734,
    output logic [7:0] inj_res_1755007861032_190,
    output logic inj_y_1755007861031_565
);
    // BEGIN: mod_comb_logic_ts1755007861031
    // BEGIN: mod_name_conflict_ts1755007861032
    logic conflict_var_ts1755007861032;
        dup_nested_if dup_nested_if_inst_1755007861032_8216 (
            .mode(inj_mode_1755007861032_625),
            .val1(inj_val1_1755007861032_103),
            .val2(inj_val2_1755007861032_202),
            .res(inj_res_1755007861032_190)
        );
    parameter int conflict_param = 1;
    assign inj_out_a_1755007861031_734 = inj_b_1755007861031_879;
    // END: mod_name_conflict_ts1755007861032

    always_comb begin
        inj_y_1755007861031_565 = inj_a_1755007861031_633 & inj_b_1755007861031_879;
    end
    // END: mod_comb_logic_ts1755007861031
endmodule

