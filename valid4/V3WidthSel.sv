module PackedVectorSelections (
    input logic [31:0] in_packed_vec_in,
    output logic [7:0] out_vec_bit_desc,
    output logic [15:0] out_vec_range_desc,
    output logic [15:0] out_vec_plus_desc,
    output logic [15:0] out_vec_minus_desc
);
    localparam int IDX_S_P = 1;
    localparam int MSB_C_P = 2;
    localparam int LSB_C_P = 1;
    localparam int WIDTH_C_P = 2;
    logic [7:0] local_packed_bytes_desc [3:0];
    always_comb begin
        local_packed_bytes_desc[0] = in_packed_vec_in[7:0];
        local_packed_bytes_desc[1] = in_packed_vec_in[15:8];
        local_packed_bytes_desc[2] = in_packed_vec_in[23:16];
        local_packed_bytes_desc[3] = in_packed_vec_in[31:24];
    end
    always_comb out_vec_bit_desc = local_packed_bytes_desc[IDX_S_P];
    always_comb out_vec_range_desc = local_packed_bytes_desc[MSB_C_P : LSB_C_P];
    always_comb out_vec_plus_desc = local_packed_bytes_desc[LSB_C_P +: WIDTH_C_P];
    always_comb out_vec_minus_desc = local_packed_bytes_desc[MSB_C_P -: WIDTH_C_P];
endmodule
module UnpackedArraySelections (
    input int in_unpacked_arr_val,
    output int out_arr_bit_sel,
    output int out_arr_slice_sel,
    output int out_arr_plus_sel
);
    localparam int IDX_P = 2;
    localparam int SLICE_LOW_IDX_P = 1;
    localparam int SLICE_HIGH_IDX_P = 3;
    localparam int PLUS_START_P = 1;
    localparam int PLUS_WIDTH_P = 2;
    int local_unpacked_arr [5];
    always_comb begin
        for(int i=0; i<5; i++) local_unpacked_arr[i] = in_unpacked_arr_val + i;
    end
    always_comb out_arr_bit_sel = local_unpacked_arr[IDX_P];
    always_comb out_arr_slice_sel = local_unpacked_arr[SLICE_LOW_IDX_P : SLICE_HIGH_IDX_P];
    always_comb out_arr_plus_sel = local_unpacked_arr[PLUS_START_P +: PLUS_WIDTH_P];
endmodule
module QueueAndStringSelections (
    input int in_dynamic_arr_init_val,
    input int in_dyn_q_idx,
    input string in_key,
    input int in_q_range_msb,
    input int in_q_range_lsb,
    input byte in_string_byte_val,
    output int out_dyn_arr_read,
    output int out_dyn_arr_write_val,
    output int out_q_at,
    output int out_q_at_unbounded,
    output int out_q_at_unbounded_minus_one,
    output int out_q_slice,
    output byte out_string_getc_val,
    output byte out_string_getcref_val,
    output int out_assoc_sel
);
    int dyn_arr [];
    int q_val [$];
    string my_string;
    int assoc_map [string];
    always_comb begin
        if (dyn_arr.size() == 0) dyn_arr = new [5];
        for (int i=0; i<5; i++) dyn_arr[i] = in_dynamic_arr_init_val + i;
        my_string = "VerilatorTestString";
        assoc_map[in_key] = in_dynamic_arr_init_val;
        if (q_val.size() < 5) q_val.push_back(in_dynamic_arr_init_val + 10);
        if (q_val.size() < 5) q_val.push_back(in_dynamic_arr_init_val + 11);
        if (q_val.size() < 5) q_val.push_back(in_dynamic_arr_init_val + 12);
        if (q_val.size() < 5) q_val.push_back(in_dynamic_arr_init_val + 13);
        if (q_val.size() < 5) q_val.push_back(in_dynamic_arr_init_val + 14);
    end
    always_comb out_dyn_arr_read = dyn_arr[in_dyn_q_idx];
    always_comb dyn_arr[in_dyn_q_idx] = in_dynamic_arr_init_val;
    always_comb out_dyn_arr_write_val = dyn_arr[in_dyn_q_idx];
    always_comb out_q_at = q_val[in_dyn_q_idx];
    always_comb out_q_at_unbounded = q_val[$];
    always_comb out_q_at_unbounded_minus_one = q_val[$ - 1];
    always_comb out_q_slice = q_val[in_q_range_msb : in_q_range_lsb];
    always_comb out_string_getc_val = my_string[in_dyn_q_idx];
    always_comb my_string[in_dyn_q_idx] = in_string_byte_val;
    always_comb out_string_getcref_val = my_string[in_dyn_q_idx];
    always_comb out_assoc_sel = assoc_map[in_key];
endmodule
module AscendingBasicTypeSelections (
    input logic [0:31] in_asc_vec_data,
    input int in_index_a,
    input int in_width_a,
    output logic out_asc_bit_sel,
    output logic [7:0] out_asc_range_sel,
    output logic [7:0] out_asc_plus_sel,
    output logic [7:0] out_asc_minus_sel
);
    logic [0:31] my_asc_vec = in_asc_vec_data;
    always_comb out_asc_bit_sel = my_asc_vec[in_index_a];
    always_comb out_asc_range_sel = my_asc_vec[in_index_a + in_width_a - 1 : in_index_a];
    always_comb out_asc_plus_sel = my_asc_vec[in_index_a +: in_width_a];
    always_comb out_asc_minus_sel = my_asc_vec[in_index_a + in_width_a - 1 -: in_width_a];
endmodule
module DescendingBasicTypeSelections (
    input logic [31:0] in_desc_vec_data,
    input int in_index_d,
    input int in_width_d,
    output logic out_desc_bit_sel,
    output logic [7:0] out_desc_range_sel,
    output logic [7:0] out_desc_plus_sel,
    output logic [7:0] out_desc_minus_sel
);
    logic [31:0] my_desc_vec = in_desc_vec_data;
    always_comb out_desc_bit_sel = my_desc_vec[in_index_d];
    always_comb out_desc_range_sel = my_desc_vec[in_index_d + in_width_d - 1 : in_index_d];
    always_comb out_desc_plus_sel = my_desc_vec[in_index_d +: in_width_d];
    always_comb out_desc_minus_sel = my_desc_vec[in_index_d + in_width_d - 1 -: in_width_d];
endmodule
module PackedStructSelections (
    input logic [31:0] in_struct_data,
    output logic out_bit_sel,
    output logic [1:0] out_struct_range_sel,
    output logic [1:0] out_struct_plus_sel,
    output logic [1:0] out_struct_minus_sel
);
    localparam int IDX_S_P = 2;
    localparam int MSB_C_P = 2;
    localparam int LSB_C_P = 1;
    localparam int WIDTH_C_P = 2;
    typedef struct packed {
        logic [7:0] bytes [3:0];
    } my_packed_struct_with_array_t;
    my_packed_struct_with_array_t local_packed_struct;
    always_comb begin
        local_packed_struct.bytes[0] = in_struct_data[7:0];
        local_packed_struct.bytes[1] = in_struct_data[15:8];
        local_packed_struct.bytes[2] = in_struct_data[23:16];
        local_packed_struct.bytes[3] = in_struct_data[31:24];
    end
    always_comb out_bit_sel = local_packed_struct[IDX_S_P];
    always_comb out_struct_range_sel = local_packed_struct[MSB_C_P : LSB_C_P];
    always_comb out_struct_plus_sel = local_packed_struct[LSB_C_P +: WIDTH_C_P];
    always_comb out_struct_minus_sel = local_packed_struct[MSB_C_P -: WIDTH_C_P];
endmodule
module TristateIndexSelPlusMinus (
    input logic [31:0] in_data,
    output logic [7:0] out_plus_val,
    output logic [7:0] out_minus_val
);
    localparam int INDEX_NORMAL = 5;
    localparam int WIDTH_W = 8;
    logic [31:0] my_vec = in_data;
    always_comb out_plus_val = my_vec[INDEX_NORMAL +: WIDTH_W];
    always_comb out_minus_val = my_vec[INDEX_NORMAL -: WIDTH_W];
endmodule
