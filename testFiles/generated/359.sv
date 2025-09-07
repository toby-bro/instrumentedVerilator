module mod_if_elseif_chained (
    input bit [7:0] in_value,
    output bit [2:0] out_category
);
always_comb begin
    if (in_value < 10) begin
        out_category = 3'd0;
    end else if (in_value < 50) begin
        out_category = 3'd1;
    end else if (in_value < 100) begin
        out_category = 3'd2;
    end else begin
        out_category = 3'd3;
    end
end
endmodule

module snippet (
    input wire clk,
    input bit [7:0] inj_in_value_1755007874844_556,
    input wire reset,
    output bit [2:0] inj_out_category_1755007874844_796
);
    mod_if_elseif_chained mod_if_elseif_chained_inst_1755007874844_9907 (
        .out_category(inj_out_category_1755007874844_796),
        .in_value(inj_in_value_1755007874844_556)
    );
endmodule

