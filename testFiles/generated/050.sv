module ArrayIndexAndPartSelect (
    input logic [31:0] data_in,
    input int index_in,
    input logic [4:0] start_bit,
    output logic bit_out,
    output logic [7:0] byte_out
);
    logic [31:0] internal_data = data_in;
    assign bit_out = internal_data[index_in];
    assign byte_out = internal_data[start_bit +: 8];
endmodule

module mod_split_nested (
    input logic clk,
    input logic cond1,
    input logic cond2,
    input logic [7:0] data_in,
    input logic reset,
    output logic [7:0] out_nested_a,
    output logic [7:0] out_nested_b
);
    logic [7:0]  split_nested_var;
    logic [7:0] other_nested_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_nested_var <= 8'b0;
            other_nested_var <= 8'b0;
        end else begin
            split_nested_var <= 8'h11; 
            other_nested_var <= 8'h22; 
            if (cond1) begin
                split_nested_var <= data_in + 10;
                other_nested_var <= data_in + 20;
                if (cond2) begin
                    split_nested_var <= data_in + 100;
                    other_nested_var <= data_in + 200;
                end
            end else begin
                split_nested_var <= data_in - 10;
                other_nested_var <= data_in - 20;
            end
        end
    end
    always_comb begin
        out_nested_a = split_nested_var;
        out_nested_b = other_nested_var;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_cond1_1755007768182_455,
    input logic inj_cond2_1755007768182_600,
    input logic [31:0] inj_data_in_1755007768183_809,
    input logic [7:0] inj_in1_1755007768182_288,
    input logic [7:0] inj_in2_1755007768182_681,
    input int inj_index_in_1755007768183_24,
    input logic inj_sel_1755007768182_724,
    input logic [4:0] inj_start_bit_1755007768183_36,
    input wire reset,
    output logic inj_bit_out_1755007768183_801,
    output logic [7:0] inj_byte_out_1755007768183_698,
    output logic [7:0] inj_out1_1755007768182_501,
    output logic [7:0] inj_out_nested_a_1755007768182_515,
    output logic [7:0] inj_out_nested_b_1755007768182_971,
    output logic inj_result_1755007768182_357
);
    // BEGIN: basic_comb_ts1755007768182
    ;
    logic [7:0] temp_wire_ts1755007768182;
        ArrayIndexAndPartSelect ArrayIndexAndPartSelect_inst_1755007768183_2946 (
            .index_in(inj_index_in_1755007768183_24),
            .start_bit(inj_start_bit_1755007768183_36),
            .bit_out(inj_bit_out_1755007768183_801),
            .byte_out(inj_byte_out_1755007768183_698),
            .data_in(inj_data_in_1755007768183_809)
        );
        // BEGIN: multiplexer_2to1_ts1755007768182
        assign inj_result_1755007768182_357 = inj_sel_1755007768182_724 ? inj_cond2_1755007768182_600 : inj_cond1_1755007768182_455;
        // END: multiplexer_2to1_ts1755007768182

        mod_split_nested mod_split_nested_inst_1755007768182_4080 (
            .out_nested_b(inj_out_nested_b_1755007768182_971),
            .clk(clk),
            .cond1(inj_cond1_1755007768182_455),
            .cond2(inj_cond2_1755007768182_600),
            .data_in(temp_wire_ts1755007768182),
            .reset(reset),
            .out_nested_a(inj_out_nested_a_1755007768182_515)
        );
    assign temp_wire_ts1755007768182 = inj_in1_1755007768182_288 + inj_in2_1755007768182_681;
    always_comb begin
        inj_out1_1755007768182_501 = temp_wire_ts1755007768182;
    end
    // END: basic_comb_ts1755007768182
endmodule

