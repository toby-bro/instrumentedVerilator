module simple_logic_b (
    input wire data_c,
    output wire data_d
);
    assign data_d = data_c;
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_data_in_1755007841784_182,
    input logic inj_enable_1755007841784_663,
    input wire reset,
    output wire inj_data_d_1755007841784_416,
    output logic [7:0] inj_out_a_1755007841784_529,
    output logic [7:0] inj_out_b_1755007841784_132
);
    // BEGIN: mod_split_comb_ts1755007841784
    logic [7:0]  split_comb_var_ts1755007841784;
    logic [7:0] other_comb_var_ts1755007841784;
        simple_logic_b simple_logic_b_inst_1755007841784_6912 (
            .data_c(clk),
            .data_d(inj_data_d_1755007841784_416)
        );
    always_comb begin
        split_comb_var_ts1755007841784 = 8'b0; 
        other_comb_var_ts1755007841784 = 8'b0;
        if (inj_enable_1755007841784_663) begin
            split_comb_var_ts1755007841784 = inj_data_in_1755007841784_182;
            other_comb_var_ts1755007841784 = inj_data_in_1755007841784_182 + 1;
        end
        inj_out_a_1755007841784_529 = split_comb_var_ts1755007841784;
        inj_out_b_1755007841784_132 = other_comb_var_ts1755007841784;
    end
    // END: mod_split_comb_ts1755007841784
endmodule

