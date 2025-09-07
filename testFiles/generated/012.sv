module typedef_struct_mod (
    input logic [15:0] packed_in,
    output logic [7:0] field2_o
);
    typedef struct packed {
        logic [7:0] field1;
        logic [7:0] field2;
    } my_packed_struct_t;
    my_packed_struct_t my_struct_var;
    always_comb begin
        my_struct_var = packed_in;
    end
    assign field2_o = my_struct_var.field2;
endmodule

module snippet (
    input wire clk,
    input logic inj_condition_y_1755007754275_636,
    input logic [7:0] inj_in2_f_1755007754276_315,
    input logic [7:0] inj_in3_f_1755007754276_730,
    input logic [7:0] inj_in_val_y_1755007754275_124,
    input logic [31:0] inj_p_in1_1755007754276_890,
    input logic [31:0] inj_p_in2_1755007754276_891,
    input logic [1:0] inj_p_mode_1755007754276_258,
    input logic [15:0] inj_packed_in_1755007754277_445,
    input wire reset,
    output logic [7:0] inj_field2_o_1755007754277_790,
    output logic [7:0] inj_inner_field_o_1755007754278_22,
    output logic [7:0] inj_out1_f_1755007754276_166,
    output logic [7:0] inj_out2_f_1755007754276_8,
    output logic [7:0] inj_out3_f_1755007754276_610,
    output logic [7:0] inj_out_vec_y_1755007754275_15,
    output logic [31:0] inj_p_out_1755007754276_211
);
    // BEGIN: split_vector_assign_ts1755007754276
    // BEGIN: more_procedural_ts1755007754276
    // BEGIN: split_independent_nb_ts1755007754277
    // BEGIN: nested_types_mod_ts1755007754278
    typedef struct packed {
        logic [7:0] inner_field_ts1755007754278;
        logic [7:0] padding_ts1755007754278;
    } inner_struct_t;
    typedef union packed {
        logic [31:0] full_word_ts1755007754278;
        struct packed {
            logic [15:0] unused_ts1755007754278;
            inner_struct_t inner_data;
        } outer_fields;
    } outer_union_t;
    outer_union_t nested_var;
    always_comb begin
        nested_var.full_word_ts1755007754278 = inj_p_in1_1755007754276_890;
    end
    assign inj_inner_field_o_1755007754278_22 = nested_var.outer_fields.inner_data.inner_field_ts1755007754278;
    // END: nested_types_mod_ts1755007754278

    typedef_struct_mod typedef_struct_mod_inst_1755007754277_614 (
        .packed_in(inj_packed_in_1755007754277_445),
        .field2_o(inj_field2_o_1755007754277_790)
    );
    always @(posedge clk) begin
        inj_out1_f_1755007754276_166 <= inj_in_val_y_1755007754275_124;
        inj_out2_f_1755007754276_8 <= inj_in2_f_1755007754276_315;
        inj_out3_f_1755007754276_610 <= inj_in3_f_1755007754276_730;
    end
    // END: split_independent_nb_ts1755007754277

    always_comb begin
        case (inj_p_mode_1755007754276_258)
            2'b00: inj_p_out_1755007754276_211 = (inj_p_in1_1755007754276_890 + inj_p_in2_1755007754276_891) * 2;
            2'b01: inj_p_out_1755007754276_211 = (inj_p_in1_1755007754276_890 - inj_p_in2_1755007754276_891) / 3; 
            2'b10: inj_p_out_1755007754276_211 = (inj_p_in1_1755007754276_890 << 4) | (inj_p_in2_1755007754276_891 >> 2);
            default: inj_p_out_1755007754276_211 = ~(inj_p_in1_1755007754276_890 ^ inj_p_in2_1755007754276_891) + 1;
        endcase
    end
    // END: more_procedural_ts1755007754276

    always @(posedge clk) begin
        if (inj_condition_y_1755007754275_636) begin
            inj_out_vec_y_1755007754275_15[3:0] <= inj_in_val_y_1755007754275_124[3:0];
            inj_out_vec_y_1755007754275_15[7:4] <= inj_in_val_y_1755007754275_124[7:4] + 1;
        end else begin
            inj_out_vec_y_1755007754275_15 <= 8'hFF;
        end
    end
    // END: split_vector_assign_ts1755007754276
endmodule

