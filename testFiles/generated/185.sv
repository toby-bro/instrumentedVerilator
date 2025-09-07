module BindSimpleModule (
    input bit in,
    output bit out
);
    assign out = in;
endmodule

module snippet (
    input wire clk,
    input logic inj_data_in_1755007815130_878,
    input logic inj_enable_in_1755007815130_176,
    input bit inj_in_1755007815130_290,
    input wire reset,
    output logic inj_data_out_1755007815130_834,
    output bit inj_out_1755007815130_147
);
    // BEGIN: sequential_register_ts1755007815131
    always_ff @(posedge clk or negedge reset) begin
        if (!reset) begin
            inj_data_out_1755007815130_834 <= 1'b0; 
        end else if (inj_enable_in_1755007815130_176) begin
            inj_data_out_1755007815130_834 <= inj_data_in_1755007815130_878; 
        end
    end
    // END: sequential_register_ts1755007815131

    BindSimpleModule BindSimpleModule_inst_1755007815130_6650 (
        .in(inj_in_1755007815130_290),
        .out(inj_out_1755007815130_147)
    );
endmodule

