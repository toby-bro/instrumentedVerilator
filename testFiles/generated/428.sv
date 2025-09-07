module range_select_indexed_packed (
    input logic [31:0] in_vec,
    input int start_index,
    input int width,
    output logic [7:0] out_down,
    output logic [7:0] out_up
);
    always_comb begin
        if (start_index >= 0 && width > 0 && start_index + width <= 32) begin
            case (width)
                1: out_up = in_vec[start_index +: 1];
                2: out_up = in_vec[start_index +: 2];
                4: out_up = in_vec[start_index +: 4];
                8: out_up = in_vec[start_index +: 8];
                default: out_up = 'x;
            endcase
        end else begin
            out_up = 'x;
        end
        if (start_index >= width - 1 && width > 0 && start_index < 32) begin
            case (width)
                1: out_down = in_vec[start_index -: 1];
                2: out_down = in_vec[start_index -: 2];
                4: out_down = in_vec[start_index -: 4];
                8: out_down = in_vec[start_index -: 8];
                default: out_down = 'x;
            endcase
        end else begin
            out_down = 'x;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic [31:0] inj_in_vec_1755007897457_491,
    input int inj_start_index_1755007897457_303,
    input int inj_width_1755007897457_109,
    input wire reset,
    output logic [7:0] inj_out_down_1755007897457_111,
    output logic [7:0] inj_out_up_1755007897457_694
);
    range_select_indexed_packed range_select_indexed_packed_inst_1755007897457_3853 (
        .start_index(inj_start_index_1755007897457_303),
        .width(inj_width_1755007897457_109),
        .out_down(inj_out_down_1755007897457_111),
        .out_up(inj_out_up_1755007897457_694),
        .in_vec(inj_in_vec_1755007897457_491)
    );
endmodule

