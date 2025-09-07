module snippet (
    input wire clk,
    input wire [3:0] inj_data_in_1755007772076_35,
    input logic [1:0] inj_in_val_1755007772076_210,
    input wire reset,
    output reg [3:0] inj_data_out_1755007772076_560,
    output reg inj_out_res_1755007772076_476
);
    // BEGIN: mod_event_implicit_ts1755007772076
    // BEGIN: case_empty_statement_ts1755007772076
    always_comb begin
        inj_out_res_1755007772076_476 = 1'b0;
        case (inj_in_val_1755007772076_210)
            2'b00: inj_out_res_1755007772076_476 = 1'b1;
            2'b01: ;
            2'b10: inj_out_res_1755007772076_476 = 1'b0;
            default: inj_out_res_1755007772076_476 = 1'b1;
        endcase
    end
    // END: case_empty_statement_ts1755007772076

    always @* begin
        inj_data_out_1755007772076_560 = inj_data_in_1755007772076_35;
    end
    // END: mod_event_implicit_ts1755007772076
endmodule

