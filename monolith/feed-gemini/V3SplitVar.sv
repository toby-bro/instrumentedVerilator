module UnpackAndPackedSplitter (
    input  logic [1:0] in_uarray_idx_a,
    input  logic [1:0] in_uarray_idx_b,
    input  logic [3:0] in_packed_val,
    input  logic [1:0] in_temp_idx_ns,
    output logic [1:0] out_unpacked_arr_0,
    output logic [1:0] out_unpacked_arr_1,
    output logic [7:0] out_packed_arr,
    output logic       out_single_bit,
    output logic       out_non_static_index_warn
);
    logic [1:0] unpacked_data[0:1] /* verilator split_var */;
    logic [7:0] packed_data        /* verilator split_var */;
    assign out_non_static_index_warn = unpacked_data[in_temp_idx_ns][0];
    always_comb begin
        unpacked_data[0][0] = in_uarray_idx_a[0];
        unpacked_data[0][1] = in_uarray_idx_a[1];
        unpacked_data[1][0] = in_uarray_idx_b[0];
        unpacked_data[1][1] = in_uarray_idx_b[1];
        out_unpacked_arr_0 = unpacked_data[0];
        out_unpacked_arr_1 = unpacked_data[1];
        packed_data[3:0] = in_packed_val;
        packed_data[7:4] = in_packed_val + 4'h1;
        out_packed_arr = packed_data;
        out_single_bit = packed_data[2];
    end
endmodule
module UnpackedSliceAndPortSplit (
    input  logic        clk,
    input  logic [3:0]  in_val_a,
    input  logic [3:0]  in_val_b,
    input  logic [7:0]  in_ff_val_0,
    input  logic [7:0]  in_ff_val_1,
    input  logic        in_cond,
    output logic [7:0]  out_packed_sliced,
    inout  logic [7:0]  inout_port_for_conn[0:1]
);
    logic [7:0] inner_packed_arr[0:1] /* verilator split_var */;
    logic [7:0] local_unpacked_for_proc_assign[0:1] /* verilator split_var */;
    logic [7:0] init_unpacked_packed[0:1] /* verilator split_var */;
    assign inout_port_for_conn[0] = local_unpacked_for_proc_assign[0];
    assign inout_port_for_conn[1] = local_unpacked_for_proc_assign[1];
    always_comb begin
        inner_packed_arr[0][3:0] = in_val_a;
        inner_packed_arr[0][7:4] = in_val_a + 4'h1;
        inner_packed_arr[1][3:0] = in_val_b;
        inner_packed_arr[1][7:4] = in_val_b + 4'h1;
        out_packed_sliced = inner_packed_arr[0][7:0];
    end
    always_ff @(posedge clk) begin
        if (in_cond) begin
            local_unpacked_for_proc_assign[0] <= in_ff_val_0;
            local_unpacked_for_proc_assign[1] <= in_ff_val_1;
        end
    end
    initial
        init_unpacked_packed[0][7:0] = 8'hAA;
endmodule
module PackedAdvancedSplit (
    input  logic [15:0] in_data_packed,
    output logic [15:0] out_data_packed,
    input  real         in_real_val,
    output real         out_real_val,
    input  logic        a_in,
    output logic        b_out,
    output logic [0:0]  c_single_bit_arr_out,
    input  logic [0:0]  c_single_bit_arr_in,
    input  logic [1:0] in_func_uarray_val_0,
    input  logic [1:0] in_func_uarray_val_1
);
    import "DPI-C" function void dpi_import_func(input logic [7:0] dpi_arg /* verilator split_var */);
    import "DPI-C" function void dpi_open_array_func(input logic [7:0] dpi_arr[] /* verilator split_var */);
    function void proto_func(input logic [7:0] arg /* verilator split_var */);
    endfunction
    function automatic logic [1:0] my_func_ref_unpacked_arg (ref logic [1:0] func_ref_unpacked_arg[0:1] /* verilator split_var */);
        logic [1:0] func_local_return[0:1] /* verilator split_var */;
        func_local_return[0] = func_ref_unpacked_arg[0];
        func_local_return[1] = func_ref_unpacked_arg[1];
        func_ref_unpacked_arg[0] = func_ref_unpacked_arg[0] + 1;
        func_ref_unpacked_arg[1] = func_ref_unpacked_arg[1] + 1;
        return func_local_return[0];
    endfunction
    function automatic void my_func_inout_arg (inout logic [7:0] func_inout_arg /* verilator split_var */);
        func_inout_arg = func_inout_arg + 1;
    endfunction
    function automatic logic [7:0] my_func_local_var (input logic [7:0] func_in_val);
        logic [7:0] func_loc_splittable /* verilator split_var */;
        func_loc_splittable = func_in_val;
        return func_loc_splittable;
    endfunction
    logic [15:0] local_packed_var /* verilator split_var */;
    real         local_real_var   /* verilator split_var */;
    logic [31:0] auto_split_var_a /* verilator split_var */;
    logic [31:0] auto_split_var_b;
    logic [31:0] auto_split_var_c;
    logic public_not_split /* verilator split_var, public */;
    logic loop_idx_candidate /* verilator split_var */;
    logic forceable_not_split /* verilator split_var, forceable */;
    logic [0:0]  c_single_bit_arr_int /* verilator split_var */;
    logic [1:0] func_uarray_arg[0:1];
    logic [1:0] func_uarray_ret_0;
    logic [7:0] func_inout_val;
    logic [7:0] func_loc_ret;
    logic [7:0] dummy_arg_for_dpi;
    always_comb begin
        logic [7:0] arr_for_dpi [0:1];
        int i_for_loop_local;
        func_inout_val = 8'h20;
        local_packed_var = in_data_packed;
        out_data_packed = local_packed_var;
        auto_split_var_b[7:0] = in_data_packed[7:0];
        auto_split_var_b[23:16] = in_data_packed[15:8];
        auto_split_var_c[15:0] = in_data_packed;
        auto_split_var_c[20:5] = in_data_packed[15:0];
        c_single_bit_arr_int[0] = c_single_bit_arr_in[0];
        c_single_bit_arr_out[0] = c_single_bit_arr_int[0];
        local_real_var = in_real_val;
        out_real_val = local_real_var;
        public_not_split = a_in;
        b_out = public_not_split;
        forceable_not_split = a_in;
        b_out = forceable_not_split;
        for (i_for_loop_local = 0; i_for_loop_local < 1; i_for_loop_local = i_for_loop_local + 1) begin
            loop_idx_candidate = i_for_loop_local;
            b_out = loop_idx_candidate;
        end
        func_uarray_arg[0] = in_func_uarray_val_0;
        func_uarray_arg[1] = in_func_uarray_val_1;
        func_uarray_ret_0 = my_func_ref_unpacked_arg(func_uarray_arg);
        my_func_inout_arg(func_inout_val);
        func_loc_ret = my_func_local_var(in_data_packed[7:0]);
        dummy_arg_for_dpi = in_data_packed[7:0];
        dpi_import_func(dummy_arg_for_dpi);
        arr_for_dpi[0] = in_data_packed[7:0];
        arr_for_dpi[1] = in_data_packed[15:8];
        dpi_open_array_func(arr_for_dpi);
        proto_func(dummy_arg_for_dpi);
    end
endmodule
module SimpleAstCellCoverage (
    input logic in_data,
    output logic out_data
);
    logic internal_sig /* verilator split_var */;
    generate
        if (1) begin : gen_block
            always_comb internal_sig = in_data;
        end
    endgenerate
    assign out_data = internal_sig;
endmodule
module UnpackArrayElementSplitter (
    input  logic [1:0] in_val,
    output logic [1:0] out_val
);
    logic [1:0] arr[0:0] /* verilator split_var */;
    assign arr[0] = in_val;
    assign out_val = arr[0];
endmodule
module SimplePackedPortSplitter (
    input  logic [7:0] in_data,
    output logic [7:0] out_data /* verilator split_var */
);
    assign out_data = in_data;
endmodule
