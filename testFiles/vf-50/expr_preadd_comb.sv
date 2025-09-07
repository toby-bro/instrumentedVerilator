module expr_preadd_comb (
    input logic [7:0] add_val_m1,
    input wire clk,
    input logic [7:0] in_val_m1,
    input logic [3:0] inj_control_1755538573337_937,
    input wire rst,
    output logic [7:0] inj_result1_1755538573337_997,
    output logic [7:0] inj_result2_1755538573337_727,
    output logic [7:0] out_sum_m1,
    output logic [7:0] var_out_m1
);
    logic [7:0] var_m1;
        // BEGIN: dup_cond_ts1755538573337
        always_comb begin
            inj_result1_1755538573337_997 = '0;
            inj_result2_1755538573337_727 = '0;
            if (inj_control_1755538573337_937[0]) begin
                inj_result1_1755538573337_997 = var_m1 + add_val_m1;
            end else begin
                inj_result1_1755538573337_997 = var_m1 - add_val_m1;
            end
            if (inj_control_1755538573337_937[1]) begin
                inj_result2_1755538573337_727 = var_m1 - add_val_m1;
            end else begin
                inj_result2_1755538573337_727 = var_m1 + add_val_m1;
            end
            case (inj_control_1755538573337_937[3:2])
                2'b00: inj_result1_1755538573337_997 = var_m1 & add_val_m1;
                2'b01: inj_result1_1755538573337_997 = var_m1 | add_val_m1;
                2'b10: inj_result2_1755538573337_727 = var_m1 & add_val_m1;
                2'b11: inj_result2_1755538573337_727 = var_m1 | add_val_m1;
                default: begin inj_result1_1755538573337_997 = '0; inj_result2_1755538573337_727 = '0; end
            endcase
            if (inj_control_1755538573337_937[0] == inj_control_1755538573337_937[1]) begin
                inj_result1_1755538573337_997 = inj_result1_1755538573337_997 + 1;
            end else if (inj_control_1755538573337_937[2] != inj_control_1755538573337_937[3]) begin
                inj_result2_1755538573337_727 = inj_result2_1755538573337_727 - 1;
            end
        end
        // END: dup_cond_ts1755538573337

    always_comb begin
        var_m1 = in_val_m1;
        out_sum_m1 = (++var_m1) + add_val_m1;
        var_out_m1 = var_m1;
    end
endmodule

