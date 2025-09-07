module snippet (
    input wire clk,
    input wire [3:0] inj_data_in_1755007832426_550,
    input wire reset,
    output reg [3:0] inj_data_out_1755007832426_981
);
    // BEGIN: mod_event_implicit_ts1755007832426
    always @* begin
        inj_data_out_1755007832426_981 = inj_data_in_1755007832426_550;
    end
    // END: mod_event_implicit_ts1755007832426
endmodule

