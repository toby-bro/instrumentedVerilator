interface MyInterface (
    input logic clk
);
    logic req;
    logic valid;
    modport master (output req, input valid, input clk);
    modport slave (input req, output valid, input clk);
endinterface
module HandleOutOfBoundsRead (
    input logic [3:0] i_addr_arr,
    input logic [3:0] i_addr_sel,
    input logic [7:0] i_vector,
    output logic [7:0] o_array_var_elem,
    output logic o_sel_var_bit
);
    parameter ARR_SIZE = 4;
    logic [7:0] my_array [0:ARR_SIZE-1];
    assign my_array[0] = 8'd10;
    assign my_array[1] = 8'd20;
    assign my_array[2] = 8'd30;
    assign my_array[3] = 8'd40;
    assign o_sel_var_bit = i_vector[i_addr_sel];
    assign o_array_var_elem = my_array[i_addr_arr];
endmodule

module SimpleLoopExample (
    input logic [7:0] in_vec,
    output logic [7:0] out_vec
);
    always_comb begin
        for (int i = 0; i < 8; i++) begin
            out_vec[i] = in_vec[7 - i];
        end
    end
endmodule

module recursive_macro_dummy (
    input logic in_bit,
    output logic out_bit
);
    `define RECURSIVE_TEST `RECURSIVE_TEST
    assign out_bit = in_bit;
endmodule

module split_seq_dependency (
    input logic clk_c,
    input logic [7:0] in_val_c,
    output logic [7:0] out_val_c
);
    logic [7:0] mid_val_c;
    always @(posedge clk_c) begin
        mid_val_c <= in_val_c + 1;
        out_val_c <= mid_val_c * 2;
    end
endmodule

module snippet #(
    parameter integer DATA_WIDTH = 8
) (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007888608_541,
    input logic [3:0] inj_i_addr_arr_1755007888607_297,
    input logic [3:0] inj_i_addr_sel_1755007888607_685,
    input logic [7:0] inj_i_vector_1755007888607_473,
    input logic inj_in_bit_1755007888607_245,
    input wire [7:0] inj_param_in_1755007888608_93,
    input wire reset,
    output logic inj_cond_out_1755007888608_739,
    output logic [4:0] inj_internal_out_1755007888608_317,
    output logic [7:0] inj_o_array_var_elem_1755007888607_503,
    output logic inj_o_sel_var_bit_1755007888607_720,
    output logic inj_out_bit_1755007888607_799,
    output logic [7:0] inj_out_val_c_1755007888609_353,
    output logic [7:0] inj_out_var_1755007888608_566,
    output logic [7:0] inj_out_vec_1755007888608_552,
    output wire [7:0] inj_param_out_1755007888608_50,
    output logic inj_sub_out_1755007888609_541,
    output logic inj_valid_out_1755007888607_336
);
    // BEGIN: ModuleWithInterface_ts1755007888607
    // BEGIN: mod_logical_not_ts1755007888608
    // BEGIN: module_with_params_ts1755007888608
    // BEGIN: not_a_hierarchical_scope_diag_mod_ts1755007888608
    logic [7:0] simple_var_nahsdm_ts1755007888608;
        // BEGIN: sub_module_ts1755007888609
        assign inj_sub_out_1755007888609_541 = !inj_in_bit_1755007888607_245;
        // END: sub_module_ts1755007888609

        split_seq_dependency split_seq_dependency_inst_1755007888609_4934 (
            .out_val_c(inj_out_val_c_1755007888609_353),
            .clk_c(clk),
            .in_val_c(simple_var_nahsdm_ts1755007888608)
        );
        // BEGIN: case_full_parallel_mod_ts1755007888608
        always @* begin
            (* full, parallel *)
            case (inj_case_expr_1755007888608_541)
                2'b00: inj_internal_out_1755007888608_317 = 1;
                2'b01: inj_internal_out_1755007888608_317 = 2;
                2'b10: inj_internal_out_1755007888608_317 = 3;
                default: inj_internal_out_1755007888608_317 = 4;
            endcase
        end
        // END: case_full_parallel_mod_ts1755007888608

    always_comb simple_var_nahsdm_ts1755007888608 = inj_i_vector_1755007888607_473;
    assign inj_out_var_1755007888608_566 = simple_var_nahsdm_ts1755007888608;
    // END: not_a_hierarchical_scope_diag_mod_ts1755007888608

    assign inj_param_out_1755007888608_50 = inj_param_in_1755007888608_93;
    // END: module_with_params_ts1755007888608

    always_comb begin
        inj_cond_out_1755007888608_739 = !inj_in_bit_1755007888607_245;
    end
    // END: mod_logical_not_ts1755007888608

    SimpleLoopExample SimpleLoopExample_inst_1755007888608_1410 (
        .in_vec(inj_i_vector_1755007888607_473),
        .out_vec(inj_out_vec_1755007888608_552)
    );
    recursive_macro_dummy recursive_macro_dummy_inst_1755007888607_5286 (
        .in_bit(inj_in_bit_1755007888607_245),
        .out_bit(inj_out_bit_1755007888607_799)
    );
    MyInterface my_if (clk);
    assign my_if.req = 1'b1;
    assign inj_valid_out_1755007888607_336 = my_if.valid;
    // END: ModuleWithInterface_ts1755007888607

    HandleOutOfBoundsRead HandleOutOfBoundsRead_inst_1755007888607_5468 (
        .i_addr_sel(inj_i_addr_sel_1755007888607_685),
        .i_vector(inj_i_vector_1755007888607_473),
        .o_array_var_elem(inj_o_array_var_elem_1755007888607_503),
        .o_sel_var_bit(inj_o_sel_var_bit_1755007888607_720),
        .i_addr_arr(inj_i_addr_arr_1755007888607_297)
    );
endmodule

