module split_complex_blocking (
    input logic [7:0] i1_r,
    input logic [7:0] i2_r,
    input logic [7:0] i3_r,
    output logic [7:0] o1_r,
    output logic [7:0] o2_r,
    output logic [7:0] o3_r
);
    logic [7:0] t1_r, t2_r;
    always @(*) begin
        t1_r = i1_r + i2_r;
        o1_r = t1_r - i3_r;
        t2_r = i2_r * i3_r;
        o2_r = t1_r + t2_r;
        o3_r = t2_r / 2;
    end
endmodule

module split_nested_if (
    input logic clk_m,
    input logic cond1_m,
    input logic cond2_m,
    input logic [7:0] val_a_m,
    input logic [7:0] val_b_m,
    input logic [7:0] val_c_m,
    output logic [7:0] result_m
);
    always @(posedge clk_m) begin
        if (cond1_m) begin
            if (cond2_m) begin
                result_m <= val_a_m;
            end else begin
                result_m <= val_b_m;
            end
        end else begin
            result_m <= val_c_m;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_cond1_m_1755007811081_213,
    input logic inj_cond2_m_1755007811081_419,
    input logic [7:0] inj_i1_r_1755007811081_20,
    input logic [7:0] inj_i3_r_1755007811081_964,
    input logic [3:0] inj_i_bind_control_1755007811080_305,
    input logic [2:0] inj_in_val_1755007811080_210,
    input logic [7:0] inj_in_vec_1755007811080_211,
    input int inj_index_in_1755007811080_226,
    input logic [15:0] inj_packed_in_1755007811085_871,
    input wire reset,
    output int inj_config_data_out_1755007811086_60,
    output logic [7:0] inj_field0_byte_o_1755007811085_605,
    output logic [7:0] inj_o1_r_1755007811081_952,
    output logic [7:0] inj_o2_r_1755007811081_797,
    output logic [7:0] inj_o3_r_1755007811081_35,
    output logic inj_o_bind_status_1755007811080_75,
    output logic inj_o_p_and_1755007811083_882,
    output logic inj_o_p_xor_1755007811083_833,
    output logic [7:0] inj_out_1755007811081_879,
    output logic inj_out_bit_1755007811080_776,
    output logic inj_out_data_pull0_1755007811084_14,
    output logic inj_out_data_pull1_1755007811084_880,
    output reg inj_out_res_1755007811080_871,
    output logic [3:0] inj_out_slice_1755007811080_935,
    output logic [7:0] inj_result_m_1755007811081_787
);
    // BEGIN: module_to_bind_ts1755007811080
    // BEGIN: casez_xz_ts1755007811080
    // BEGIN: element_select_packed_ts1755007811080
    // BEGIN: simple_assign_ts1755007811081
    // BEGIN: primitive_example_ts1755007811083
    // BEGIN: module_with_unconnected_drive_ts1755007811084
    // BEGIN: typedef_union_mod_ts1755007811085
    typedef union packed {
        logic [15:0] word_ts1755007811085;
        logic [1:0][7:0] byte_fields_ts1755007811085;
    } my_packed_union_t;
    my_packed_union_t my_union_var;
    // BEGIN: PragmaProtectOptions_ts1755007811086
`ifdef SLANG_PRAGMA
`protect encoding (enctype="base64", line_length=76, bytes=1024)
`endif
`ifdef SLANG_PRAGMA
`protect license (library="my_project_lib", entry="start_feature_A", match=42, feature="feature_set_B", exit="end_feature_A")
`endif
`ifdef SLANG_PRAGMA
`protect reset
`endif
`ifdef SLANG_PRAGMA
`protect viewport (object="design.module_a.instance_b.register_c", access="read-only")
`endif
assign inj_config_data_out_1755007811086_60 = inj_index_in_1755007811080_226 + 1;
    // END: PragmaProtectOptions_ts1755007811086

    always_comb begin
        my_union_var.word_ts1755007811085 = inj_packed_in_1755007811085_871;
    end
    assign inj_field0_byte_o_1755007811085_605 = my_union_var.byte_fields_ts1755007811085[0];
    // END: typedef_union_mod_ts1755007811085

    assign inj_out_data_pull1_1755007811084_880 = inj_cond2_m_1755007811081_419;
    assign inj_out_data_pull0_1755007811084_14 = ~inj_cond2_m_1755007811081_419;
    // END: module_with_unconnected_drive_ts1755007811084

    and (inj_o_p_and_1755007811083_882, inj_cond2_m_1755007811081_419, inj_cond1_m_1755007811081_213);
    xor (inj_o_p_xor_1755007811083_833, inj_cond2_m_1755007811081_419, inj_cond1_m_1755007811081_213);
    // END: primitive_example_ts1755007811083

    split_nested_if split_nested_if_inst_1755007811081_2202 (
        .val_b_m(inj_in_vec_1755007811080_211),
        .val_c_m(inj_i3_r_1755007811081_964),
        .result_m(inj_result_m_1755007811081_787),
        .clk_m(clk),
        .cond1_m(inj_cond1_m_1755007811081_213),
        .cond2_m(inj_cond2_m_1755007811081_419),
        .val_a_m(inj_i1_r_1755007811081_20)
    );
    split_complex_blocking split_complex_blocking_inst_1755007811081_1936 (
        .i2_r(inj_in_vec_1755007811080_211),
        .i3_r(inj_i3_r_1755007811081_964),
        .o1_r(inj_o1_r_1755007811081_952),
        .o2_r(inj_o2_r_1755007811081_797),
        .o3_r(inj_o3_r_1755007811081_35),
        .i1_r(inj_i1_r_1755007811081_20)
    );
    assign inj_out_1755007811081_879 = inj_in_vec_1755007811080_211;
    // END: simple_assign_ts1755007811081

    always_comb begin
        if (inj_index_in_1755007811080_226 >= 0 && inj_index_in_1755007811080_226 < 8)
            inj_out_bit_1755007811080_776 = inj_in_vec_1755007811080_211[inj_index_in_1755007811080_226];
        else
            inj_out_bit_1755007811080_776 = 'x; 
    end
    assign inj_out_slice_1755007811080_935 = inj_in_vec_1755007811080_211[6:3];
    // END: element_select_packed_ts1755007811080

    always_comb begin
        inj_out_res_1755007811080_871 = 1'b0;
        casez (inj_in_val_1755007811080_210)
            3'b1??: inj_out_res_1755007811080_871 = 1'b1;
            3'b0z?: inj_out_res_1755007811080_871 = 1'b0;
            default: inj_out_res_1755007811080_871 = 1'b1;
        endcase
    end
    // END: casez_xz_ts1755007811080

    always_comb inj_o_bind_status_1755007811080_75 = |inj_i_bind_control_1755007811080_305;
    // END: module_to_bind_ts1755007811080
endmodule

