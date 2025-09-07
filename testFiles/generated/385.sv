module sequential_register (
    input logic clk,
    input logic data_in,
    input logic enable_in,
    input logic reset_n,
    output logic data_out
);
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            data_out <= 1'b0; 
        end else if (enable_in) begin
            data_out <= data_in; 
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_data_in_1755007883306_290,
    input logic inj_enable_in_1755007883306_339,
    input wire reset,
    output logic inj_data_out_1755007883306_478
);
    sequential_register sequential_register_inst_1755007883306_5910 (
        .enable_in(inj_enable_in_1755007883306_339),
        .reset_n(reset),
        .data_out(inj_data_out_1755007883306_478),
        .clk(clk),
        .data_in(inj_data_in_1755007883306_290)
    );
endmodule

