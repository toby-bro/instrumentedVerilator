module SelBit_Types (
    input logic [31:0]  clk,
    input logic [7:0]   idx_8bit,
    input logic [3:0]   idx_4bit,
    input logic [31:0]  assoc_key_in,
    input logic [39:0]  wide_idx_in,
    output logic [7:0]  vec_bit_out,
    output int          arr_bit_out,
    output int          assoc_out,
    output int          dyn_out,
    output int          q_out_front,
    output int          q_out_back,
    output int          q_out_back_offset,
    output byte         str_char_out,
    output logic        scalar_bit_out,
    output logic        packed_struct_bit_out,
    output logic        packed_struct_wide_idx_bit_out,
    output int          tri_warn_bit_out,
    output logic [7:0]  byte_array_sel_bit_out
);
    logic [31:0] vector_data = 32'hFEEDC0DE;
    int unpacked_array[10];
    int assoc_array[*];
    int dyn_array[];
    int my_queue[$];
    string my_string = "Verilator";
    typedef struct packed {
        logic [7:0] byte0;
        logic [7:0] byte1;
        logic [7:0] byte2;
        logic [7:0] byte3;
    } packed_bytes_t;
    packed_bytes_t ps_data = '{byte0: 8'h11, byte1: 8'h22, byte2: 8'h33, byte3: 8'h44};
    logic [3:0] scalar_data = 4'b1010;
    localparam logic [7:0] VALID_INDEX_FOR_WARN = 8'h0;
    logic [7:0] my_bytes[3:0];
    always_comb begin
        for (int i = 0; i < 10; i++) begin
            unpacked_array[i] = i;
        end
        assoc_array[32'hABCD] = 100;
        assoc_array[32'h1234] = 200;
        dyn_array = new[5];
        for (int i = 0; i < 5; i++) begin
            dyn_array[i] = i * 10;
        end
        my_queue = {};
        my_queue.push_front(10);
        my_queue.push_back(20);
        my_queue.push_back(30);
        for (int i = 0; i < 4; i++) begin
            my_bytes[i] = 8'hAA + i;
        end
        vec_bit_out = vector_data[idx_8bit];
        arr_bit_out = unpacked_array[idx_4bit];
        assoc_out = assoc_array[assoc_key_in];
        dyn_out = dyn_array[idx_4bit];
        q_out_front = my_queue[idx_4bit];
        q_out_back = my_queue[$];
        q_out_back_offset = my_queue[$-1];
        str_char_out = my_string[idx_4bit];
        scalar_bit_out = scalar_data[idx_4bit % 4];
        packed_struct_bit_out = ps_data[idx_4bit];
        packed_struct_wide_idx_bit_out = ps_data[wide_idx_in];
        tri_warn_bit_out = vector_data[VALID_INDEX_FOR_WARN];
        byte_array_sel_bit_out = my_bytes[idx_4bit];
    end
endmodule
module SelExtract_Ranges (
    input logic [31:0]  clk,
    input logic [4:0]   dummy_hi,
    input logic [4:0]   dummy_lo,
    output logic [7:0]  vec_part_desc,
    output logic [7:0]  vec_part_asc,
    output logic [7:0]  asc_vec_part_range_warn,
    output logic [15:0] vec_part_partial,
    output int          arr_part_out[4],
    output int          arr_single_elem_slice_out[1],
    output int          q_slice_front_out[$],
    output int          q_slice_back_out[$],
    output int          q_slice_front_back_out[$],
    output logic [7:0]  scalar_part_out,
    output logic [15:0] packed_struct_part_out
);
    logic [31:0] vector_data = 32'hDEADBEEF;
    logic [0:31] asc_vector_data = 32'hBEEFDEAD;
    int unpacked_array[10];
    int my_queue_ext[$];
    typedef struct packed {
        logic [7:0] field_a;
        logic [7:0] field_b;
        logic [7:0] field_c;
        logic [7:0] field_d;
    } packed_s_t;
    packed_s_t ps_extract_data = '{field_a: 8'hAA, field_b: 8'hBB, field_c: 8'hCC, field_d: 8'hDD};
    logic [15:0] scalar_word = 16'hABCD;
    always_comb begin
        for (int i = 0; i < 10; i++) begin
            unpacked_array[i] = i * 100;
        end
        my_queue_ext = {};
        my_queue_ext.push_back(10);
        my_queue_ext.push_back(20);
        my_queue_ext.push_back(30);
        my_queue_ext.push_back(40);
        my_queue_ext.push_back(50);
        my_queue_ext.push_back(60);
        vec_part_desc = vector_data[15:8];
        vec_part_asc = vector_data[15:8];
        asc_vec_part_range_warn = asc_vector_data[8:15];
        vec_part_partial = vector_data[31:16];
        arr_part_out = unpacked_array[2:5];
        arr_single_elem_slice_out = unpacked_array[2:2];
        q_slice_front_out = my_queue_ext[3:1];
        q_slice_back_out = my_queue_ext[$:1];
        q_slice_front_back_out = my_queue_ext[3:$];
        scalar_part_out = scalar_word[15:8];
        packed_struct_part_out = ps_extract_data[15:0];
    end
endmodule
module SelPlusMinus_Ranges (
    input logic [31:0]  clk,
    input logic [7:0]   base_idx,
    output logic [7:0]  vec_plus_out,
    output logic [7:0]  vec_minus_out,
    output int          arr_plus_out[8],
    output int          arr_minus_out[8],
    output logic [7:0]  scalar_plus_out,
    output logic [7:0]  scalar_minus_out,
    output logic [7:0]  ps_plus_out,
    output logic [7:0]  ps_minus_out,
    output logic [7:0]  asc_vec_plus_out,
    output logic [7:0]  asc_vec_minus_out
);
    localparam int PM_WIDTH = 8;
    logic [31:0] vector_data = 32'h12345678;
    int unpacked_array[10];
    logic [15:0] scalar_data = 16'hABCD;
    logic [0:7] asc_vec = 8'h5A;
    typedef struct packed {
        logic [7:0] byte0;
        logic [7:0] byte1;
        logic [7:0] byte2;
        logic [7:0] byte3;
    } packed_s_pm_t;
    packed_s_pm_t ps_pm_data = '{byte0: 8'hAA, byte1: 8'hBB, byte2: 8'hCC, byte3: 8'hDD};
    always_comb begin
        for (int i = 0; i < 10; i++) begin
            unpacked_array[i] = i * 11;
        end
        vec_plus_out = vector_data[base_idx +: PM_WIDTH];
        vec_minus_out = vector_data[base_idx -: PM_WIDTH];
        arr_plus_out = unpacked_array[base_idx +: PM_WIDTH];
        arr_minus_out = unpacked_array[base_idx -: PM_WIDTH];
        scalar_plus_out = scalar_data[base_idx +: PM_WIDTH];
        scalar_minus_out = scalar_data[base_idx -: PM_WIDTH];
        ps_plus_out = ps_pm_data[base_idx +: PM_WIDTH];
        ps_minus_out = ps_pm_data[base_idx -: PM_WIDTH];
        asc_vec_plus_out = asc_vec[base_idx +: PM_WIDTH];
        asc_vec_minus_out = asc_vec[base_idx -: PM_WIDTH];
    end
endmodule
module SelPlusMinus_WarnTri (
    input logic dummy_in,
    output logic dummy_out
);
    logic [31:0] data = 32'h0;
    logic [7:0] warn_out;
    localparam logic [7:0] NON_X_INDEX_FOR_WARN = 8'h0;
    always_comb begin
        warn_out = data[NON_X_INDEX_FOR_WARN +: 8];
    end
    assign dummy_out = warn_out[0];
endmodule
