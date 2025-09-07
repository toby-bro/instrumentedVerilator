module Mod_UnpackedSplit (
    input logic [1:0] in_sig,
    input logic [0:1][1:0] in_ua_arr_port /* verilator split_var */, 
    output logic [1:0] out_sig,
    output logic [0:1][1:0] out_ua_arr_port /* verilator split_var */,
    input logic func_in,
    output logic func_out,
    output logic initial_output
);
    logic [1:0] unpacked_array_var[0:2] /* verilator split_var */;
    logic [1:0] unpacked_logic_array_for_test[0:1] /* verilator split_var */;
    real scalar_real_wreal_test /* verilator split_var */;
    logic [1:0] initial_target_var[0:0] /* verilator split_var */;
    always_comb unpacked_array_var[0][0] = in_sig[0];
    always_comb begin
        unpacked_array_var[1][0] = in_sig[1];
        unpacked_array_var[1][1] = ~in_sig[0];
        out_sig[0] = unpacked_array_var[0][0];
    end
    always_comb begin
        logic [1:0] temp_slice;
        temp_slice = unpacked_array_var[0][1:0];
        out_sig[1] = temp_slice[0];
    end
    always_comb begin
        unpacked_array_var[2] = in_ua_arr_port[0]; 
        out_ua_arr_port[1] = unpacked_array_var[2];
    end
    always_comb begin
        unpacked_logic_array_for_test[0] = 2'b01;
        unpacked_logic_array_for_test[1] = ~unpacked_logic_array_for_test[0];
    end
    always_comb begin
        scalar_real_wreal_test = 3.14;
        out_sig = (scalar_real_wreal_test > 0.0) ? 2'b10 : 2'b01;
    end
    task process_local_unpacked_array;
        logic [1:0] local_unpacked_array[0:1] /* verilator split_var */; 
        logic temp_val;
        always_comb begin
            local_unpacked_array[0][0] = func_in;
            temp_val = local_unpacked_array[0][0];
            func_out = temp_val;
        end
    endtask
    logic dummy_call_var_func;
    always_comb begin
        process_local_unpacked_array();
        dummy_call_var_func = func_out; 
    end
    initial initial_target_var[0][0] = 1'b1;
    always_comb initial_output = initial_target_var[0][0];
    always_comb begin
        logic dummy;
        dummy = unpacked_array_var[100][0]; 
    end
    always_comb begin
        logic dummy;
        dummy = unpacked_array_var[in_sig[0]][0]; 
    end
endmodule
module Mod_PackedSplit (
    input logic [7:0] in_packed_data,
    input logic [7:0] in_packed_port /* verilator split_var */, 
    output logic [7:0] out_packed_data,
    output logic [7:0] out_packed_port /* verilator split_var */
);
    logic [15:0] packed_vec /* verilator split_var */;
    typedef struct packed {
        logic s_a;
        bit [2:0] s_b;
    } my_ps_t;
    my_ps_t packed_struct_var /* verilator split_var */;
    struct {
        logic us_c;
        int us_d; 
    } unpacked_struct_var /* verilator split_var */;
    logic [15:0] auto_split_target; 
    always_comb begin
        packed_vec = {in_packed_data, 8'h00}; 
        packed_vec[0] = in_packed_data[0]; 
        packed_vec[15:8] = in_packed_data; 
        out_packed_data = packed_vec[7:0];
    end
    always_comb begin
        packed_struct_var.s_a = in_packed_data[1];
        packed_struct_var.s_b = in_packed_data[4:2];
        out_packed_data[0] = packed_struct_var.s_a;
    end
    always_comb begin
        unpacked_struct_var.us_c = in_packed_data[5];
        unpacked_struct_var.us_d = 10; 
        out_packed_data[1] = unpacked_struct_var.us_c;
    end
    always_comb begin
        auto_split_target[3:0] = in_packed_data[3:0];
        auto_split_target[7:4] = in_packed_data[7:4];
        auto_split_target[11:8] = in_packed_data[3:0] + 1;
        auto_split_target[15:12] = in_packed_data[7:4] + 1;
        out_packed_data[2] = auto_split_target[0];
    end
    always_comb @(posedge packed_vec[0] or negedge packed_struct_var.s_a) begin
    end
    always_comb begin
        out_packed_port = in_packed_port;
    end
    task my_local_packed_task;
        logic [7:0] func_local_packed_var /* verilator split_var */;
        always_comb begin
            func_local_packed_var = in_packed_data; 
        end
    endtask
    always_comb begin
        my_local_packed_task(); 
    end
endmodule
module Mod_CannotSplit (
    input logic [7:0] in_val,
    input int in_idx,
    output logic out_flag,
    inout logic bad_inout_port /* verilator split_var */ 
);
    logic [0:0] single_bit_var /* verilator split_var */; 
    int int_packed_var /* verilator split_var */; 
    logic scalar_no_dim /* verilator split_var */; 
    logic [7:0] dynamic_idx_packed_var /* verilator split_var */; 
    logic /* verilator public */ public_variable /* verilator split_var */; 
    logic forceable_variable /* verilator forceable */ /* verilator split_var */; 
    always_comb begin
        single_bit_var = in_val[0];
        int_packed_var = in_val;
        scalar_no_dim = in_val[1];
        if (in_idx < 8 && in_idx >= 0) begin 
            dynamic_idx_packed_var[in_idx] = in_val[2]; 
        end
        public_variable = in_val[3];
        forceable_variable = in_val[4];
        bad_inout_port = in_val[5]; 
        out_flag = single_bit_var | scalar_no_dim;
    end
    always_comb begin
        int /* verilator split_var */ loop_idx_cannot_split = 0; 
        for (loop_idx_cannot_split = 0; loop_idx_cannot_split < 8; loop_idx_cannot_split++) begin
            if (loop_idx_cannot_split == 4) out_flag = 1'b1;
        end
        out_flag = (out_flag || loop_idx_cannot_split == 8); 
    end
    task my_task_prototype();
    endtask
    task my_task_with_ref (ref logic ref_arg /* verilator split_var */);
        ref_arg = ~ref_arg;
    endtask
    logic task_arg_var = 1'b0;
    always_comb begin
        my_task_with_ref(task_arg_var); 
        out_flag = task_arg_var;
    end
endmodule
