module snippet (
    input wire clk,
    input wire [3:0] inj_data_in_1755007860737_201,
    input wire reset,
    output reg [3:0] inj_data_out_1755007860737_825
);
    // BEGIN: mod_event_implicit_ts1755007860737
    always @* begin
        inj_data_out_1755007860737_825 = inj_data_in_1755007860737_201;
    end
    // END: mod_event_implicit_ts1755007860737
endmodule

