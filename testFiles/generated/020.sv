module ModMultipleAlways (
    input logic clk_a,
    input logic clk_b,
    input logic din_a,
    input logic din_b,
    input logic rst_n,
    output logic dout_a,
    output logic dout_b
);
    always @(posedge clk_a or negedge rst_n) begin 
    if (!rst_n) begin 
        dout_a <= 1'b0;
    end else begin
        dout_a <= din_a; 
    end
    end
    always @(posedge clk_b) begin 
    dout_b <= din_b; 
    end
endmodule

module simple_for_loop (
    input logic [7:0] in_data,
    output logic [7:0] out_sum
);
    logic [7:0] sum;
    always_comb begin
        sum = 8'h00;
        for (int i = 0; i < 5; i = i + 1) begin
            sum = sum + in_data;
        end
        out_sum = sum;
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_b_1755007756976_494,
    input logic [7:0] inj_c_1755007756976_370,
    input logic inj_din_a_1755007756975_847,
    input logic inj_din_b_1755007756975_478,
    input logic [7:0] inj_in_data_1755007756976_788,
    input wire reset,
    output logic inj_anded_1755007756976_38,
    output logic inj_diff_1755007756976_168,
    output logic inj_dout_a_1755007756975_839,
    output logic inj_dout_b_1755007756975_6,
    output logic inj_ored_1755007756976_592,
    output logic [7:0] inj_out_sum_1755007756976_269,
    output logic [7:0] inj_sum_1755007756976_68,
    output logic inj_xored_1755007756976_198
);
    // BEGIN: more_ops_ts1755007756976
    assign inj_sum_1755007756976_68 = inj_in_data_1755007756976_788 + inj_b_1755007756976_494;
    assign inj_diff_1755007756976_168 = inj_in_data_1755007756976_788 > inj_c_1755007756976_370;
    assign inj_anded_1755007756976_38 = inj_in_data_1755007756976_788 & inj_b_1755007756976_494;
    assign inj_ored_1755007756976_592 = inj_in_data_1755007756976_788 | inj_c_1755007756976_370;
    assign inj_xored_1755007756976_198 = inj_in_data_1755007756976_788 ^ inj_b_1755007756976_494;
    // END: more_ops_ts1755007756976

    simple_for_loop simple_for_loop_inst_1755007756976_6621 (
        .in_data(inj_in_data_1755007756976_788),
        .out_sum(inj_out_sum_1755007756976_269)
    );
    ModMultipleAlways ModMultipleAlways_inst_1755007756975_1053 (
        .din_b(inj_din_b_1755007756975_478),
        .rst_n(reset),
        .dout_a(inj_dout_a_1755007756975_839),
        .dout_b(inj_dout_b_1755007756975_6),
        .clk_a(clk),
        .clk_b(clk),
        .din_a(inj_din_a_1755007756975_847)
    );
endmodule

