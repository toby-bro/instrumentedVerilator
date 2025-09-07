module child_concat_output (
    input logic dummy_in,
    output logic [7:0] data
);
    assign data = dummy_in ? 8'hAA : 8'h55;
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

module module_with_unconnected_drive (
    input logic in_data,
    output logic out_data_pull0,
    output logic out_data_pull1
);
    assign out_data_pull1 = in_data;
    assign out_data_pull0 = ~in_data;
endmodule

module sub_module (
    input logic sub_in,
    output logic sub_out
);
    assign sub_out = !sub_in;
endmodule

module unsupported_logand_expr (
    input logic [7:0] in_a_m9,
    input logic [7:0] in_b_m9,
    output logic out_m9
);
    logic [7:0] var_m9;
    always_comb begin
        var_m9 = in_a_m9;
        if ((var_m9 > 10) && (in_b_m9 < 5)) begin
            out_m9 = 1;
        end else begin
            out_m9 = 0;
        end
        var_m9++;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_cond2_1755007798197_245,
    input logic inj_dummy_in_1755007798197_211,
    input bit inj_in_1755007798199_81,
    input logic [7:0] inj_in_val_a_l_1755007798197_334,
    input logic [7:0] inj_in_val_b_l_1755007798197_910,
    input logic [15:0] inj_packed_in_1755007798198_361,
    input logic [1:0] inj_sel_1755007798197_182,
    input wire reset,
    output logic [7:0] inj_data_1755007798197_318,
    output logic [7:0] inj_field2_o_1755007798198_889,
    output bit inj_out_1755007798199_551,
    output logic [7:0] inj_out_case_a_1755007798197_589,
    output logic [7:0] inj_out_case_b_1755007798197_29,
    output logic inj_out_data_pull0_1755007798197_716,
    output logic inj_out_data_pull1_1755007798197_861,
    output logic inj_out_m9_1755007798199_746,
    output logic [7:0] inj_out_nested_a_1755007798197_548,
    output logic [7:0] inj_out_nested_b_1755007798197_769,
    output logic [7:0] inj_out_reg_t_1755007798199_259,
    output logic [8:0] inj_out_val_c_l_1755007798197_417,
    output logic [7:0] inj_out_val_d_l_1755007798197_759,
    output logic inj_sub_out_1755007798198_694
);
    // BEGIN: split_inputs_outputs_only_ts1755007798197
    // BEGIN: mod_split_case_ts1755007798197
    logic [7:0]  split_case_var_ts1755007798197;
    logic [7:0] other_case_var_ts1755007798197;
        // BEGIN: BindSimpleModule_ts1755007798199
        assign inj_out_1755007798199_551 = inj_in_1755007798199_81;
        // END: BindSimpleModule_ts1755007798199

        // BEGIN: split_if_empty_branches_ts1755007798199
        always @(posedge clk) begin
            if (inj_cond2_1755007798197_245) begin
            end else begin
            end
        end
        // END: split_if_empty_branches_ts1755007798199

        unsupported_logand_expr unsupported_logand_expr_inst_1755007798199_8032 (
            .in_b_m9(split_case_var_ts1755007798197),
            .out_m9(inj_out_m9_1755007798199_746),
            .in_a_m9(inj_in_val_a_l_1755007798197_334)
        );
        // BEGIN: typedef_struct_public_mod_ts1755007798198
        typedef struct packed {
            logic [7:0] field1_ts1755007798198;
            logic [7:0] field2_ts1755007798198;
        } my_public_packed_struct_t;
        my_public_packed_struct_t my_struct_var;
        always_comb begin
            my_struct_var = inj_packed_in_1755007798198_361;
        end
        assign inj_field2_o_1755007798198_889 = my_struct_var.field2_ts1755007798198;
        // END: typedef_struct_public_mod_ts1755007798198

        sub_module sub_module_inst_1755007798198_2478 (
            .sub_in(inj_dummy_in_1755007798197_211),
            .sub_out(inj_sub_out_1755007798198_694)
        );
        module_with_unconnected_drive module_with_unconnected_drive_inst_1755007798197_6272 (
            .in_data(inj_dummy_in_1755007798197_211),
            .out_data_pull0(inj_out_data_pull0_1755007798197_716),
            .out_data_pull1(inj_out_data_pull1_1755007798197_861)
        );
    always_comb begin
        split_case_var_ts1755007798197 = 8'hFF;
        other_case_var_ts1755007798197 = 8'hAA;
        case (inj_sel_1755007798197_182)
            2'b00: begin
                split_case_var_ts1755007798197 = inj_in_val_b_l_1755007798197_910 + 5;
                other_case_var_ts1755007798197 = inj_in_val_b_l_1755007798197_910 + 6;
            end
            2'b01: begin
                split_case_var_ts1755007798197 = inj_in_val_b_l_1755007798197_910 - 5;
                other_case_var_ts1755007798197 = inj_in_val_b_l_1755007798197_910 - 6;
            end
            default: begin
                split_case_var_ts1755007798197 = inj_in_val_b_l_1755007798197_910;
                other_case_var_ts1755007798197 = inj_in_val_b_l_1755007798197_910;
            end
        endcase
        inj_out_case_a_1755007798197_589 = split_case_var_ts1755007798197;
        inj_out_case_b_1755007798197_29 = other_case_var_ts1755007798197;
    end
    // END: mod_split_case_ts1755007798197

    mod_split_nested mod_split_nested_inst_1755007798197_1707 (
        .out_nested_b(inj_out_nested_b_1755007798197_769),
        .clk(clk),
        .cond1(inj_dummy_in_1755007798197_211),
        .cond2(inj_cond2_1755007798197_245),
        .data_in(inj_in_val_a_l_1755007798197_334),
        .reset(reset),
        .out_nested_a(inj_out_nested_a_1755007798197_548)
    );
    child_concat_output child_concat_output_inst_1755007798197_9098 (
        .dummy_in(inj_dummy_in_1755007798197_211),
        .data(inj_data_1755007798197_318)
    );
    always @(*) begin
        inj_out_val_c_l_1755007798197_417 = inj_in_val_a_l_1755007798197_334 + inj_in_val_b_l_1755007798197_910;
        inj_out_val_d_l_1755007798197_759 = inj_in_val_a_l_1755007798197_334 - inj_in_val_b_l_1755007798197_910;
    end
    // END: split_inputs_outputs_only_ts1755007798197
endmodule

