module snippet (
    input wire clk,
    input bit [2:0] inj_in_state_case_1755007858066_581,
    input wire reset,
    output bit inj_out_priority_case_1755007858066_57,
    output bit inj_out_unique_case_1755007858066_990
);
    // BEGIN: mod_case_unique_priority_ts1755007858066
always_comb begin
    inj_out_unique_case_1755007858066_990 = 1'b0;
    unique case (inj_in_state_case_1755007858066_581)
        3'd0: inj_out_unique_case_1755007858066_990 = 1'b0;
        3'd1: inj_out_unique_case_1755007858066_990 = 1'b1;
        3'd2: inj_out_unique_case_1755007858066_990 = 1'b0;
        3'd1: inj_out_unique_case_1755007858066_990 = 1'b1;
        default: inj_out_unique_case_1755007858066_990 = 1'b1;
    endcase
end
always_comb begin
    inj_out_priority_case_1755007858066_57 = 1'b0;
    priority case (inj_in_state_case_1755007858066_581)
        3'd0: inj_out_priority_case_1755007858066_57 = 1'b0;
        3'd1: inj_out_priority_case_1755007858066_57 = 1'b1;
        3'd2: inj_out_priority_case_1755007858066_57 = 1'b0;
        3'd1: inj_out_priority_case_1755007858066_57 = 1'b1;
        default: inj_out_priority_case_1755007858066_57 = 1'b1;
    endcase
end
    // END: mod_case_unique_priority_ts1755007858066
endmodule

