module member_access_packed_union (
    input logic [31:0] in_val,
    input bit select_a,
    output logic [31:0] out_val
);
    typedef union packed {
        logic [31:0] a; 
        logic [31:0] b; 
    } my_packed_union;
    my_packed_union union_var;
    always_comb begin
        if (select_a)
            union_var.a = in_val;
        else
            union_var.b = in_val[31:0];
        out_val = union_var.a;
    end
endmodule

module split_basic_blocking (
    input logic [7:0] in1_a,
    output logic [7:0] out1_a
);
    always @(*) begin
        out1_a = in1_a;
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_in2_1755007920590_329,
    input logic [7:0] inj_in3_1755007920590_747,
    input logic [7:0] inj_in_1755007920589_815,
    input logic inj_in_a_1755007920590_474,
    input logic [31:0] inj_in_val_1755007920589_588,
    input logic [15:0] inj_packed_in_1755007920589_505,
    input bit inj_select_a_1755007920589_804,
    input wire reset,
    output logic [7:0] inj_field2_o_1755007920589_44,
    output logic inj_nand_out_1755007920590_242,
    output logic inj_nor_out_1755007920590_247,
    output logic [7:0] inj_out1_a_1755007920591_223,
    output logic [7:0] inj_out_1755007920589_468,
    output logic inj_out_a_1755007920590_340,
    output logic [31:0] inj_out_val_1755007920589_251,
    output logic [7:0] inj_out_var_1755007920591_913,
    output logic inj_xnor_out_1755007920590_396
);
    // BEGIN: sub_inst_array_mod_ts1755007920589
    // BEGIN: typedef_struct_public_mod_ts1755007920589
    typedef struct packed {
        logic [7:0] field1_ts1755007920589;
        logic [7:0] field2_ts1755007920589;
    } my_public_packed_struct_t;
    my_public_packed_struct_t my_struct_var;
    // BEGIN: mod_name_conflict_ts1755007920590
    logic conflict_var_ts1755007920590;
    parameter int conflict_param = 1;
    // BEGIN: not_a_hierarchical_scope_diag_mod_ts1755007920591
    logic [7:0] simple_var_nahsdm_ts1755007920591;
    always_comb simple_var_nahsdm_ts1755007920591 = inj_in2_1755007920590_329;
    assign inj_out_var_1755007920591_913 = simple_var_nahsdm_ts1755007920591;
    // END: not_a_hierarchical_scope_diag_mod_ts1755007920591

    split_basic_blocking split_basic_blocking_inst_1755007920591_8121 (
        .in1_a(inj_in2_1755007920590_329),
        .out1_a(inj_out1_a_1755007920591_223)
    );
    assign inj_out_a_1755007920590_340 = inj_in_a_1755007920590_474;
    // END: mod_name_conflict_ts1755007920590

    // BEGIN: remaining_reduction_ops_ts1755007920590
    assign inj_nand_out_1755007920590_242 = ~&inj_in_1755007920589_815;
    assign inj_nor_out_1755007920590_247 = ~|inj_in2_1755007920590_329;
    assign inj_xnor_out_1755007920590_396 = ^~inj_in3_1755007920590_747;
    // END: remaining_reduction_ops_ts1755007920590

    always_comb begin
        my_struct_var = inj_packed_in_1755007920589_505;
    end
    assign inj_field2_o_1755007920589_44 = my_struct_var.field2_ts1755007920589;
    // END: typedef_struct_public_mod_ts1755007920589

    assign inj_out_1755007920589_468 = inj_in_1755007920589_815;
    // END: sub_inst_array_mod_ts1755007920589

    member_access_packed_union member_access_packed_union_inst_1755007920589_1359 (
        .in_val(inj_in_val_1755007920589_588),
        .select_a(inj_select_a_1755007920589_804),
        .out_val(inj_out_val_1755007920589_251)
    );
endmodule

