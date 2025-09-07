module snippet (
    input wire clk,
    input logic [2:0] inj_mode_1755007825309_512,
    input logic [7:0] inj_val1_1755007825309_561,
    input logic [7:0] inj_val2_1755007825309_911,
    input wire reset,
    output logic [7:0] inj_out_1755007825310_448,
    output logic [7:0] inj_res_1755007825309_563
);
    // BEGIN: dup_nested_if_ts1755007825309
    // BEGIN: sequential_always_assign_ts1755007825310
    always @(posedge clk) begin
        inj_out_1755007825310_448 <= inj_val1_1755007825309_561;
    end
    // END: sequential_always_assign_ts1755007825310

    always_comb begin
        inj_res_1755007825309_563 = '0;
        if (inj_mode_1755007825309_512 == 3'b001) begin
            if (inj_val1_1755007825309_561 > inj_val2_1755007825309_911) begin
                inj_res_1755007825309_563 = inj_val1_1755007825309_561 + inj_val2_1755007825309_911;
            end else begin
                inj_res_1755007825309_563 = inj_val1_1755007825309_561 - inj_val2_1755007825309_911;
            end
        end else if (inj_mode_1755007825309_512 == 3'b010) begin
            if (inj_val1_1755007825309_561 > inj_val2_1755007825309_911) begin
                inj_res_1755007825309_563 = inj_val1_1755007825309_561 + inj_val2_1755007825309_911;
            end else begin
                inj_res_1755007825309_563 = inj_val1_1755007825309_561 - inj_val2_1755007825309_911;
            end
        end else if (inj_mode_1755007825309_512 == 3'b011) begin
            if (inj_val1_1755007825309_561 < inj_val2_1755007825309_911) begin
                inj_res_1755007825309_563 = inj_val1_1755007825309_561 * inj_val2_1755007825309_911;
            end else begin
                inj_res_1755007825309_563 = inj_val1_1755007825309_561 / ((inj_val2_1755007825309_911 == 0) ? 1 : inj_val2_1755007825309_911);
            end
        end else if (inj_mode_1755007825309_512 == 3'b100) begin
            if (inj_val1_1755007825309_561 != inj_val2_1755007825309_911) begin
                if (inj_val1_1755007825309_561 > inj_val2_1755007825309_911) inj_res_1755007825309_563 = inj_val1_1755007825309_561;
                else inj_res_1755007825309_563 = inj_val2_1755007825309_911;
            end else begin
                inj_res_1755007825309_563 = inj_val1_1755007825309_561 + inj_val2_1755007825309_911;
            end
        end
        else begin
            inj_res_1755007825309_563 = inj_val1_1755007825309_561 ^ inj_val2_1755007825309_911;
        end
    end
    // END: dup_nested_if_ts1755007825309
endmodule

