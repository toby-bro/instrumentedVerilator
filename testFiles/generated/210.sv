module expr_postsub_comb (
    input logic [7:0] in_val_m2,
    input logic [7:0] sub_val_m2,
    output logic [7:0] out_diff_m2,
    output logic [7:0] var_out_m2
);
    logic [7:0] var_m2;
    always_comb begin
        var_m2 = in_val_m2;
        out_diff_m2 = (var_m2--) - sub_val_m2;
        var_out_m2 = var_m2;
    end
endmodule

module invalid_this_diag_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module non_ansi_basic (
    non_ansi_a,
    non_ansi_basic_input,
    non_ansi_b,
    non_ansi_basic_output
);
    input wire non_ansi_a;
    output reg non_ansi_b;
    input logic non_ansi_basic_input;
    output logic non_ansi_basic_output;
    always_comb begin
        non_ansi_b = non_ansi_a;
        non_ansi_basic_output = non_ansi_basic_input;
    end
endmodule

module wide_bus_ops (
    input wire [63:0] wide_a,
    input wire [63:0] wide_b,
    output wire [127:0] concat_out,
    output wire [7:0] reduce_xor_out,
    output wire [63:0] wide_sum
);
    assign wide_sum = wide_a + wide_b;
    assign reduce_xor_out = ^wide_a[63:0];
    assign concat_out = {wide_a, wide_b};
endmodule

module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007823522_281,
    input logic [3:0] inj_case_inside_val_1755007823522_881,
    input bit inj_cfg_in_1755007823523_16,
    input logic [15:0] inj_dividend_mod_1755007823523_516,
    input int inj_in_val_1755007823526_400,
    input logic [7:0] inj_in_val_m2_1755007823523_418,
    input logic [31:0] inj_input_pa_1755007823525_355,
    input logic [15:0] inj_numerator_1755007823523_997,
    input logic inj_sub_in_1755007823524_496,
    input logic [7:0] inj_sub_val_m2_1755007823523_928,
    input wire [63:0] inj_wide_a_1755007823524_490,
    input wire [63:0] inj_wide_b_1755007823524_327,
    input wire reset,
    output bit inj_cfg_out_1755007823523_477,
    output wire [127:0] inj_concat_out_1755007823524_668,
    output logic [4:0] inj_internal_out_1755007823522_389,
    output reg inj_non_ansi_b_1755007823527_680,
    output logic inj_non_ansi_basic_output_1755007823527_672,
    output logic [7:0] inj_out_diff_m2_1755007823523_855,
    output int inj_out_val_1755007823526_20,
    output logic [7:0] inj_output_pa_1755007823525_461,
    output logic [7:0] inj_output_pa_element1_1755007823525_407,
    output logic [15:0] inj_quotient_1755007823523_330,
    output wire [7:0] inj_reduce_xor_out_1755007823524_515,
    output logic [7:0] inj_remainder_1755007823523_55,
    output logic inj_sub_out_1755007823524_685,
    output logic [7:0] inj_var_out_m2_1755007823523_768,
    output wire [63:0] inj_wide_sum_1755007823524_132
);
    // BEGIN: case_unique_casez_reordered_mod_ts1755007823522
    // BEGIN: Module_ConfigKeywords_ts1755007823523
    // BEGIN: div_mod_ops_ts1755007823523
    // BEGIN: sub_module_ts1755007823524
    // BEGIN: module_packed_array_ts1755007823525
    logic [7:0] my_packed_array[0:3] ;
    non_ansi_basic non_ansi_basic_inst_1755007823527_5411 (
        .non_ansi_b(inj_non_ansi_b_1755007823527_680),
        .non_ansi_basic_input(inj_sub_in_1755007823524_496),
        .non_ansi_basic_output(inj_non_ansi_basic_output_1755007823527_672),
        .non_ansi_a(clk)
    );
    invalid_this_diag_mod invalid_this_diag_mod_inst_1755007823526_1567 (
        .in_val(inj_in_val_1755007823526_400),
        .out_val(inj_out_val_1755007823526_20)
    );
    always_comb begin
        if (inj_sub_in_1755007823524_496) begin
            my_packed_array[0] = inj_input_pa_1755007823525_355[7:0];
            my_packed_array[1] = inj_input_pa_1755007823525_355[15:8];
            my_packed_array[2] = inj_input_pa_1755007823525_355[23:16];
            my_packed_array[3] = my_packed_array[0] + my_packed_array[1];
        end else begin
            my_packed_array[0] = 8'h0;
            my_packed_array[1] = 8'h0;
            my_packed_array[2] = 8'h0;
            my_packed_array[3] = 8'h0;
        end
        my_packed_array[0][3:0] = inj_case_inside_val_1755007823522_881;
    end
    assign inj_output_pa_1755007823525_461 = my_packed_array[3];
    assign inj_output_pa_element1_1755007823525_407 = my_packed_array[1];
    // END: module_packed_array_ts1755007823525

    wide_bus_ops wide_bus_ops_inst_1755007823524_3280 (
        .concat_out(inj_concat_out_1755007823524_668),
        .reduce_xor_out(inj_reduce_xor_out_1755007823524_515),
        .wide_sum(inj_wide_sum_1755007823524_132),
        .wide_a(inj_wide_a_1755007823524_490),
        .wide_b(inj_wide_b_1755007823524_327)
    );
    assign inj_sub_out_1755007823524_685 = !inj_sub_in_1755007823524_496;
    // END: sub_module_ts1755007823524

    assign inj_quotient_1755007823523_330 = (inj_in_val_m2_1755007823523_418 == 0) ? 16'hFFFF : (inj_numerator_1755007823523_997 / inj_in_val_m2_1755007823523_418); 
    assign inj_remainder_1755007823523_55 = (inj_sub_val_m2_1755007823523_928 == 0) ? 8'hFF : (inj_dividend_mod_1755007823523_516 % inj_sub_val_m2_1755007823523_928);
    // END: div_mod_ops_ts1755007823523

    expr_postsub_comb expr_postsub_comb_inst_1755007823523_3189 (
        .in_val_m2(inj_in_val_m2_1755007823523_418),
        .sub_val_m2(inj_sub_val_m2_1755007823523_928),
        .out_diff_m2(inj_out_diff_m2_1755007823523_855),
        .var_out_m2(inj_var_out_m2_1755007823523_768)
    );
    assign inj_cfg_out_1755007823523_477 = inj_cfg_in_1755007823523_16;
    // END: Module_ConfigKeywords_ts1755007823523

    always @* begin
        unique casez ({inj_case_expr_1755007823522_281[0], inj_case_inside_val_1755007823522_881[3:2], inj_case_expr_1755007823522_281[1]})
            4'b1?0?: inj_internal_out_1755007823522_389 = 30;
            4'b?101: inj_internal_out_1755007823522_389 = 31;  
            4'b0?1?: inj_internal_out_1755007823522_389 = 32;
            4'b1?1?: inj_internal_out_1755007823522_389 = 33;  
            4'b?111: inj_internal_out_1755007823522_389 = 34;  
        endcase
    end
    // END: case_unique_casez_reordered_mod_ts1755007823522
endmodule

