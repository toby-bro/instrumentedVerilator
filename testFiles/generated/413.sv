module cu_timeunit_mod (
    input logic clk,
    output logic reset
);
    logic internal_sig;
    always_ff @(posedge clk) begin
        reset <= 1'b0;
        internal_sig = clk;
    end
endmodule

module snippet (
    input wire clk,
    input wire reset,
    output logic inj_reset_1755007892359_98
);
    cu_timeunit_mod cu_timeunit_mod_inst_1755007892359_8009 (
        .clk(clk),
        .reset(inj_reset_1755007892359_98)
    );
endmodule

