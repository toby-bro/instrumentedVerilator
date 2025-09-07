module mod_split_ff (
    input logic clk,
    input logic [7:0] data_in,
    input logic reset,
    output logic [7:0] out_reg_a,
    output logic [7:0] out_reg_b
);
    logic [7:0]  split_reg_var;
    logic [7:0] other_reg_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_reg_var <= 8'b0;
            other_reg_var <= 8'b0;
            out_reg_a <= 8'b0;
            out_reg_b <= 8'b0;
        end else begin
            split_reg_var <= data_in;
            other_reg_var <= data_in + 2;
            out_reg_a <= split_reg_var;
            out_reg_b <= other_reg_var;
        end
    end
endmodule

module snippet (
    input wire clk,
    input bit inj_cfg_in_1755007758029_109,
    input logic [7:0] inj_data_in_1755007758029_194,
    input wire reset,
    output bit inj_cfg_out_1755007758029_244,
    output logic [7:0] inj_out_reg_a_1755007758029_499,
    output logic [7:0] inj_out_reg_b_1755007758029_636
);
    // BEGIN: Module_ConfigKeywords_ts1755007758029
    mod_split_ff mod_split_ff_inst_1755007758029_9712 (
        .data_in(inj_data_in_1755007758029_194),
        .reset(reset),
        .out_reg_a(inj_out_reg_a_1755007758029_499),
        .out_reg_b(inj_out_reg_b_1755007758029_636),
        .clk(clk)
    );
    assign inj_cfg_out_1755007758029_244 = inj_cfg_in_1755007758029_109;
    // END: Module_ConfigKeywords_ts1755007758029
endmodule

