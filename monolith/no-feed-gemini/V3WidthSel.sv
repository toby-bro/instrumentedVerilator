module SelBitAndStringModule (
    input  logic [31:0]      packed_vec_in,
    input  logic [1:32]      ascending_packed_vec_in,
    input  logic [7:0]       unpacked_array_in [1:16],
    input  int               index_in_pos,
    input  int               index_in_neg_range,
    input  int               assoc_key_in,
    input  logic [3:0]       dyn_array_idx_in,
    input  byte              string_char_idx_in,
    input  logic [15:0]      scalar_vector_in,
    input  logic [3:0]       packed_struct_field_idx_in,
    output logic             packed_vec_bit_out,
    output logic             ascending_packed_vec_bit_out,
    output logic [7:0]       unpacked_array_el_out,
    output int               assoc_val_out,
    output int               dyn_array_el_out,
    output byte              string_char_out,
    output logic             scalar_vector_bit_out,
    output logic             packed_struct_bit_out,
    output logic             queue_head_out,
    output logic             queue_back_out,
    output logic             queue_back_offset_out
);
    assign packed_vec_bit_out = packed_vec_in[index_in_pos];
    assign ascending_packed_vec_bit_out = ascending_packed_vec_in[index_in_pos];
    assign unpacked_array_el_out = unpacked_array_in[index_in_neg_range];
    int assoc_array_mem [int];
    initial begin
        assoc_array_mem[0] = 100;
        assoc_array_mem[1] = 200;
    end
    assign assoc_val_out = assoc_array_mem[assoc_key_in];
    int dyn_array_mem [];
    always_comb begin
        if (dyn_array_idx_in < 5) begin
            dyn_array_mem = new[5];
            for (int i=0; i<5; i++) dyn_array_mem[i] = i*10;
        end else begin
            dyn_array_mem = new[0];
        end
    end
    assign dyn_array_el_out = dyn_array_mem[dyn_array_idx_in];
    logic queue_mem [$];
    initial begin
        queue_mem.push_back(1'b0);
        queue_mem.push_back(1'b1);
        queue_mem.push_back(1'b0);
    end
    assign queue_head_out = queue_mem[0];
    assign queue_back_out = queue_mem[$];
    assign queue_back_offset_out = queue_mem[$ - 1];
    string my_string = "HelloVerilog";
    assign string_char_out = my_string[string_char_idx_in];
    assign scalar_vector_bit_out = scalar_vector_in[index_in_pos];
    typedef struct packed {
        logic [7:0] field_a;
        logic [7:0] field_b;
        logic [15:0] field_c;
    } my_packed_struct_t;
    my_packed_struct_t packed_struct_inst;
    assign packed_struct_inst.field_a = 8'hAA;
    assign packed_struct_inst.field_b = 8'hBB;
    assign packed_struct_inst.field_c = 16'hCCCC;
    assign packed_struct_bit_out = packed_struct_inst.field_a[packed_struct_field_idx_in];
endmodule
module SelExtractAndQueueModule (
    input  logic [63:0]      packed_vec_in_ext,
    input  logic [7:0]       unpacked_array_in_ext [0:7],
    input  logic [1:16]      ascending_vector_in,
    input  int               msb_idx_in,
    input  int               lsb_idx_in,
    input  int               msb_idx_in_warn,
    input  int               lsb_idx_in_warn,
    output logic [7:0]       packed_vec_slice_out,
    output logic [7:0]       unpacked_array_slice_out [0:0],
    output logic [3:0]       queue_slice_front_front_out [$],
    output logic [3:0]       queue_slice_front_back_out [$],
    output logic [3:0]       queue_slice_back_back_out [$],
    output logic [7:0]       scalar_vector_slice_out,
    output logic [7:0]       ascending_vector_slice_out,
    output logic [7:0]       packed_struct_slice_out
);
    assign packed_vec_slice_out = packed_vec_in_ext[msb_idx_in_warn : lsb_idx_in_warn];
    assign unpacked_array_slice_out = unpacked_array_in_ext[msb_idx_in : lsb_idx_in];
    logic [3:0] queue_test_q [$];
    initial begin
        queue_test_q = {4'h0, 4'h1, 4'h2, 4'h3, 4'h4, 4'h5, 4'h6, 4'h7};
    end
    assign queue_slice_front_front_out = queue_test_q[msb_idx_in : lsb_idx_in];
    assign queue_slice_front_back_out  = queue_test_q[msb_idx_in : $ - 1];
    assign queue_slice_back_back_out   = queue_test_q[$ - 1 : $ - 3];
    assign scalar_vector_slice_out = packed_vec_in_ext[msb_idx_in : lsb_idx_in];
    logic [1:16] ascending_vector_internal;
    assign ascending_vector_internal = ascending_vector_in;
    assign ascending_vector_slice_out = ascending_vector_internal[msb_idx_in : lsb_idx_in];
    typedef struct packed {
        logic [7:0] field_d;
        logic [7:0] field_e;
        logic [15:0] field_f;
    } my_packed_struct_ext_t;
    my_packed_struct_ext_t packed_struct_ext_inst;
    assign packed_struct_ext_inst.field_d = 8'hDD;
    assign packed_struct_ext_inst.field_e = 8'hEE;
    assign packed_struct_ext_inst.field_f = 16'hFFFF;
    assign packed_struct_slice_out = packed_struct_ext_inst.field_d[msb_idx_in : lsb_idx_in];
endmodule
module SelPlusMinusModule (
    input  logic [31:0]      data_vector_pm,
    input  logic [7:0]       unpacked_array_pm_in [0:31],
    input  int               base_idx_pm,
    input  int               ascending_base_idx_pm,
    input  int               width_val_pm,
    output logic [7:0]       plus_slice_out_vec,
    output logic [7:0]       minus_slice_out_vec,
    output logic [7:0]       plus_slice_out_unpacked,
    output logic [7:0]       minus_slice_out_unpacked,
    output logic [7:0]       plus_slice_out_ascending,
    output logic [7:0]       minus_slice_out_ascending,
    output logic [15:0]      plus_slice_out_packed_array,
    output logic [15:0]      minus_slice_out_packed_array,
    output logic [15:0]      plus_slice_out_packed_struct,
    output logic [15:0]      minus_slice_out_packed_struct,
    output logic [7:0]       slice_out_large_width,
    output logic [7:0]       slice_out_negative_width
);
    assign plus_slice_out_vec = data_vector_pm[base_idx_pm +: width_val_pm];
    assign minus_slice_out_vec = data_vector_pm[base_idx_pm -: width_val_pm];
    assign plus_slice_out_unpacked = unpacked_array_pm_in[base_idx_pm +: 1];
    assign minus_slice_out_unpacked = unpacked_array_pm_in[base_idx_pm -: 1];
    logic [1:32] ascending_vector_pm;
    assign ascending_vector_pm = data_vector_pm;
    assign plus_slice_out_ascending = ascending_vector_pm[ascending_base_idx_pm +: width_val_pm];
    assign minus_slice_out_ascending = ascending_vector_pm[ascending_base_idx_pm -: width_val_pm];
    typedef struct packed { logic [7:0] data; } element_t;
    element_t packed_array_of_elements [3:0];
    assign packed_array_of_elements[0].data = 8'h00;
    assign packed_array_of_elements[1].data = 8'h11;
    assign packed_array_of_elements[2].data = 8'h22;
    assign packed_array_of_elements[3].data = 8'h33;
    assign plus_slice_out_packed_array = packed_array_of_elements[base_idx_pm +: 2];
    assign minus_slice_out_packed_array = packed_array_of_elements[base_idx_pm -: 2];
    typedef struct packed {
        logic [7:0] field_g;
        logic [7:0] field_h;
        logic [7:0] field_i;
        logic [7:0] field_j;
    } my_packed_struct_pm_t;
    my_packed_struct_pm_t packed_struct_pm_inst;
    assign packed_struct_pm_inst.field_g = 8'h44;
    assign packed_struct_pm_inst.field_h = 8'h55;
    assign packed_struct_pm_inst.field_i = 8'h66;
    assign packed_struct_pm_inst.field_j = 8'h77;
    assign plus_slice_out_packed_struct = packed_struct_pm_inst[base_idx_pm +: width_val_pm];
    assign minus_slice_out_packed_struct = packed_struct_pm_inst[base_idx_pm -: width_val_pm];
    assign slice_out_large_width    = data_vector_pm[0 +: 2_000_000_000];
    assign slice_out_negative_width = data_vector_pm[0 +: -1];
endmodule
module IndexErrorAndSpecialCasesModule (
    input  logic [7:0]       data_in_err,
    input  int               dynamic_idx,
    output logic             bit_out_err_x,
    output logic [7:0]       slice_out_err_non_const_extract,
    output logic [7:0]       slice_out_err_non_const_width_pm,
    output logic             bit_out_subneg_lhs_const
);
    assign bit_out_err_x = data_in_err[2'bX];
    assign slice_out_err_non_const_extract = data_in_err[7 : dynamic_idx];
    assign slice_out_err_non_const_width_pm = data_in_err[0 +: dynamic_idx];
    logic [1:8] ascending_vec_subneg;
    assign ascending_vec_subneg = 8'hAA;
    assign bit_out_subneg_lhs_const = ascending_vec_subneg[dynamic_idx];
endmodule
