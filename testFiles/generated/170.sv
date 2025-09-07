module non_ansi_concat_port (
    concat_port_input,
    concat_port_output,
    non_ansi_i,
    non_ansi_j
);
    output logic [1:0] non_ansi_i;
    output logic [1:0] non_ansi_j;
    input logic concat_port_input;
    output logic concat_port_output;
    assign non_ansi_i = 2'b10;
    assign non_ansi_j = 2'b01;
    assign concat_port_output = concat_port_input;
endmodule

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module snippet (
    input wire clk,
    input logic inj_a_1755007810096_242,
    input logic inj_b_1755007810096_4,
    input logic [1:0] inj_case_expr_1755007810096_547,
    input logic [7:0] inj_vif_data_1755007810096_603,
    input wire reset,
    output logic inj_concat_port_output_1755007810097_890,
    output logic inj_dummy_out_1755007810096_110,
    output logic [4:0] inj_internal_out_1755007810096_328,
    output logic [1:0] inj_non_ansi_i_1755007810097_621,
    output logic [1:0] inj_non_ansi_j_1755007810097_985,
    output logic [7:0] inj_out_data_1755007810096_706,
    output logic inj_out_valid_1755007810096_617,
    output logic inj_sum_1755007810096_83
);
    // BEGIN: virtual_interface_lookup_mod_ts1755007810096
    // BEGIN: case_unique0_violating_mod_ts1755007810097
    non_ansi_concat_port non_ansi_concat_port_inst_1755007810097_327 (
        .non_ansi_j(inj_non_ansi_j_1755007810097_985),
        .concat_port_input(inj_a_1755007810096_242),
        .concat_port_output(inj_concat_port_output_1755007810097_890),
        .non_ansi_i(inj_non_ansi_i_1755007810097_621)
    );
    always @* begin
        unique0 casez (inj_case_expr_1755007810096_547)
            2'b1?: inj_internal_out_1755007810096_328 = 8;
            2'b11: inj_internal_out_1755007810096_328 = 9;  
            2'b?1: inj_internal_out_1755007810096_328 = 10; 
            2'b00: inj_internal_out_1755007810096_328 = 11; 
        endcase
    end
    // END: case_unique0_violating_mod_ts1755007810097

    always_comb begin
        inj_out_data_1755007810096_706  = inj_vif_data_1755007810096_603;
        inj_out_valid_1755007810096_617 = inj_b_1755007810096_4;
        inj_dummy_out_1755007810096_110 = inj_a_1755007810096_242;
    end
    // END: virtual_interface_lookup_mod_ts1755007810096

    simple_adder simple_adder_inst_1755007810096_3025 (
        .a(inj_a_1755007810096_242),
        .b(inj_b_1755007810096_4),
        .sum(inj_sum_1755007810096_83)
    );
endmodule

