module snippet (
    input wire clk,
    input logic inj_condition_t_1755007816658_967,
    input logic [7:0] inj_in_val_t_1755007816658_124,
    input wire reset,
    output logic [7:0] inj_out_reg_t_1755007816658_399
);
    // BEGIN: split_if_empty_branches_ts1755007816658
    always @(posedge clk) begin
        if (inj_condition_t_1755007816658_967) begin
        end else begin
        end
    end
    // END: split_if_empty_branches_ts1755007816658
endmodule

