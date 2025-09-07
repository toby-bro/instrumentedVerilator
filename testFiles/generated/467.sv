module Parameterized #(
    parameter int WIDTH = 8
) (
    input logic [7:0] din,
    output logic [7:0] dout
);
    assign dout = din;
endmodule

module snippet (
    input wire clk,
    input logic inj_data_value_1755007910336_886,
    input logic [7:0] inj_din_1755007910335_227,
    input logic [7:0] inj_in2_1755007910335_192,
    input wire [7:0] inj_in_val1_1755007910335_431,
    input wire [7:0] inj_in_val2_1755007910335_610,
    input logic inj_level1_en_1755007910336_590,
    input logic inj_level2_en_1755007910336_182,
    input wire [1:0] inj_select_idx_1755007910335_241,
    input wire reset,
    output logic [7:0] inj_dout_1755007910335_992,
    output logic [7:0] inj_out1_1755007910335_576,
    output logic [7:0] inj_out2_1755007910335_300,
    output wire [3:0] inj_out_element_1755007910335_915,
    output logic [7:0] inj_out_ternary_result_1755007910335_300,
    output logic inj_result_out_1755007910336_248
);
    // BEGIN: module_ternary_ts1755007910335
    // BEGIN: always_multi_stmt_unhandled_ts1755007910335
    // BEGIN: unpacked_array_module_ts1755007910336
    logic [3:0] data_array_ts1755007910336 [4];
        // BEGIN: nested_blocks_ts1755007910336
        always_comb begin : main_block 
            inj_result_out_1755007910336_248 = 1'b0; 
            if (inj_level1_en_1755007910336_590) begin : inner_block1 
                if (inj_level2_en_1755007910336_182) begin : inner_block2 
                    inj_result_out_1755007910336_248 = inj_data_value_1755007910336_886;
                end 
            end 
        end
        // END: nested_blocks_ts1755007910336

    always @(*) begin
        data_array_ts1755007910336[0] = inj_in_val1_1755007910335_431[3:0];
        data_array_ts1755007910336[1] = inj_in_val1_1755007910335_431[7:4];
        data_array_ts1755007910336[2] = 4'd8;
        data_array_ts1755007910336[3] = 4'd12;
    end
    assign inj_out_element_1755007910335_915 = data_array_ts1755007910336[inj_select_idx_1755007910335_241];
    // END: unpacked_array_module_ts1755007910336

    always_comb begin
        inj_out1_1755007910335_576 = inj_din_1755007910335_227;
        inj_out2_1755007910335_300 = inj_in2_1755007910335_192;
    end
    // END: always_multi_stmt_unhandled_ts1755007910335

    Parameterized Parameterized_inst_1755007910335_5797 (
        .dout(inj_dout_1755007910335_992),
        .din(inj_din_1755007910335_227)
    );
    always_comb begin
    inj_out_ternary_result_1755007910335_300 = clk ? inj_in_val1_1755007910335_431 : inj_in_val2_1755007910335_610;
    end
    // END: module_ternary_ts1755007910335
endmodule

