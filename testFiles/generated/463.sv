module snippet (
    input wire clk,
    input wire [7:0] inj_d_in_1755007908987_73,
    input logic [7:0] inj_in_data_1755007908987_377,
    input logic [15:0] inj_in_vec_1755007908987_49,
    input logic [31:0] inj_nested_in_1755007908988_446,
    input wire reset,
    output logic [7:0] inj_inner_field_o_1755007908988_229,
    output logic [7:0] inj_out_slice_be_1755007908987_963,
    output logic [7:0] inj_out_slice_le_1755007908987_419,
    output logic [7:0] inj_out_sum_1755007908987_671,
    output reg [7:0] inj_q_out_1755007908987_478
);
    // BEGIN: simple_for_loop_ts1755007908987
    logic [7:0] sum_ts1755007908987;
        // BEGIN: nested_types_mod_ts1755007908988
        typedef struct packed {
            logic [7:0] inner_field_ts1755007908988;
            logic [7:0] padding_ts1755007908988;
        } inner_struct_t;
        typedef union packed {
            logic [31:0] full_word_ts1755007908988;
            struct packed {
                logic [15:0] unused_ts1755007908988;
                inner_struct_t inner_data;
            } outer_fields;
        } outer_union_t;
        outer_union_t nested_var;
        always_comb begin
            nested_var.full_word_ts1755007908988 = inj_nested_in_1755007908988_446;
        end
        assign inj_inner_field_o_1755007908988_229 = nested_var.outer_fields.inner_data.inner_field_ts1755007908988;
        // END: nested_types_mod_ts1755007908988

        // BEGIN: range_select_simple_packed_ts1755007908988
        assign inj_out_slice_be_1755007908987_963 = inj_in_vec_1755007908987_49[7:0]; 
        assign inj_out_slice_le_1755007908987_419 = inj_in_vec_1755007908987_49[7:0]; 
        // END: range_select_simple_packed_ts1755007908988

        // BEGIN: Seq_DFF_ts1755007908987
        always_ff @(posedge clk or posedge reset) begin
            if (reset) begin
                inj_q_out_1755007908987_478 <= 8'b0;
            end else begin
                inj_q_out_1755007908987_478 <= inj_d_in_1755007908987_73;
            end
        end
        // END: Seq_DFF_ts1755007908987

    always_comb begin
        sum_ts1755007908987 = 8'h00;
        for (int i = 0; i < 5; i = i + 1) begin
            sum_ts1755007908987 = sum_ts1755007908987 + inj_in_data_1755007908987_377;
        end
        inj_out_sum_1755007908987_671 = sum_ts1755007908987;
    end
    // END: simple_for_loop_ts1755007908987
endmodule

