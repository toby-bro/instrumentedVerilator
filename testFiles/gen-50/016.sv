module mod_always_event (
    input logic clk,
    input logic in,
    input logic rst,
    output logic out
);
    always @(posedge clk or negedge rst) begin
        if (!rst) begin
            out <= 1'b0;
        end else begin
            out <= in;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_in_1755007755633_835,
    input int inj_in_val_1755007755634_254,
    input wire [15:0] inj_value1_1755007755634_868,
    input wire [15:0] inj_value2_1755007755634_834,
    input wire reset,
    output logic inj_out_1755007755633_872,
    output logic inj_out_a_1755007755634_544,
    output int inj_out_val_1755007755634_860,
    output reg [15:0] inj_result_val_1755007755634_742
);
    // BEGIN: Comb_IfElse_ts1755007755634
    // BEGIN: mod_name_conflict_ts1755007755634
    logic conflict_var_ts1755007755634;
        // BEGIN: super_outside_class_diag_mod_ts1755007755634
        assign inj_out_val_1755007755634_860 = inj_in_val_1755007755634_254;
        // END: super_outside_class_diag_mod_ts1755007755634

    parameter int conflict_param = 1;
    assign inj_out_a_1755007755634_544 = inj_in_1755007755633_835;
    // END: mod_name_conflict_ts1755007755634

    always_comb begin
        if (clk) begin
            inj_result_val_1755007755634_742 = inj_value1_1755007755634_868;
        end else begin
            inj_result_val_1755007755634_742 = inj_value2_1755007755634_834;
        end
    end
    // END: Comb_IfElse_ts1755007755634

    mod_always_event mod_always_event_inst_1755007755633_4647 (
        .out(inj_out_1755007755633_872),
        .clk(clk),
        .rst(reset),
        .in(inj_in_1755007755633_835)
    );
endmodule

