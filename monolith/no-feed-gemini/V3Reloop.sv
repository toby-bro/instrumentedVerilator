module module_array_to_array_reloop (
    input  logic         clk,
    input  logic [7:0]   source_data_in  [19:0], 
    output logic [7:0]   destination_data_out [19:0]  
);
    always_ff @(posedge clk) begin
        destination_data_out[0]  <= source_data_in[2];
        destination_data_out[1]  <= source_data_in[3];
        destination_data_out[2]  <= source_data_in[4];
        destination_data_out[3]  <= source_data_in[5];
        destination_data_out[4]  <= source_data_in[6];
        destination_data_out[5]  <= source_data_in[7];
        destination_data_out[6]  <= source_data_in[8];
        destination_data_out[7]  <= source_data_in[9];
        destination_data_out[8]  <= source_data_in[10];
        destination_data_out[9]  <= source_data_in[11];
        destination_data_out[10] <= source_data_in[12];
        destination_data_out[11] <= source_data_in[13];
        destination_data_out[12] <= source_data_in[14];
        destination_data_out[13] <= source_data_in[15];
        destination_data_out[14] <= source_data_in[16]; 
    end
endmodule
module module_const_to_array_reloop (
    input  logic enable_fill,
    output logic [15:0] config_register_array [19:0]
);
    parameter C_MAGIC_VALUE = 16'hDEAD;
    always_comb begin
        if (enable_fill) begin
            config_register_array[0]  = C_MAGIC_VALUE;
            config_register_array[1]  = C_MAGIC_VALUE;
            config_register_array[2]  = C_MAGIC_VALUE;
            config_register_array[3]  = C_MAGIC_VALUE;
            config_register_array[4]  = C_MAGIC_VALUE;
            config_register_array[5]  = C_MAGIC_VALUE;
            config_register_array[6]  = C_MAGIC_VALUE;
            config_register_array[7]  = C_MAGIC_VALUE;
            config_register_array[8]  = C_MAGIC_VALUE;
            config_register_array[9]  = C_MAGIC_VALUE;
            config_register_array[10] = C_MAGIC_VALUE;
            config_register_array[11] = C_MAGIC_VALUE;
            config_register_array[12] = C_MAGIC_VALUE;
            config_register_array[13] = C_MAGIC_VALUE;
            config_register_array[14] = C_MAGIC_VALUE;
        end else begin
            config_register_array[0] = 16'h0000;
            config_register_array[1] = 16'hFFFF; 
            config_register_array[2] = 16'h0123;
        end
    end
endmodule
module module_mixed_reloop_patterns (
    input  logic [7:0]   scalar_input_val,
    input  logic [3:0]   dynamic_index,
    input  logic [7:0]   source_data_bus [15:0],
    output logic [7:0]   dest_data_bus   [15:0],
    output logic [7:0]   result_scalar_out
);
    logic [7:0] self_modifying_array [15:0];
    always_comb begin
        for (int i=0; i<16; i++) begin
            self_modifying_array[i] = i;
        end
        dest_data_bus[0] = source_data_bus[0];
        dest_data_bus[1] = source_data_bus[1];
        dest_data_bus[2] = source_data_bus[2]; 
        result_scalar_out = scalar_input_val;
        dest_data_bus[dynamic_index]     = source_data_bus[dynamic_index + 1];
        dest_data_bus[dynamic_index + 1] = source_data_bus[dynamic_index + 2];
        dest_data_bus[10] = source_data_bus[8]; 
        dest_data_bus[11] = source_data_bus[9];
        dest_data_bus[12] = source_data_bus[10];
        dest_data_bus[13] = source_data_bus[11];
        dest_data_bus[14] = source_data_bus[12]; 
        self_modifying_array[0] = self_modifying_array[1];
        self_modifying_array[1] = self_modifying_array[2];
        self_modifying_array[2] = self_modifying_array[3];
        self_modifying_array[3] = self_modifying_array[4];
        self_modifying_array[4] = self_modifying_array[5];
        self_modifying_array[5] = self_modifying_array[6];
        self_modifying_array[6] = self_modifying_array[7];
        self_modifying_array[7] = self_modifying_array[8];
        self_modifying_array[8] = self_modifying_array[9];
        self_modifying_array[9] = self_modifying_array[10]; 
    end
endmodule
module module_function_task_reloop (
    input  logic [1:0]  sel_func,
    input  logic [7:0]  input_val [9:0],
    output logic [7:0]  output_val [9:0],
    output logic [7:0]  func_result_out,
    output logic [7:0]  task_result_out
);
    logic [7:0] local_array_f [9:0];
    logic [7:0] local_array_t [9:0];
    function automatic logic [7:0] process_array_f;
        input logic [7:0] src_arr [9:0]; 
        output logic [7:0] dest_arr [9:0]; 
        begin
            dest_arr[0] = 8'h11;
            dest_arr[1] = 8'h11;
            dest_arr[2] = 8'h11;
            dest_arr[3] = 8'h11;
            dest_arr[4] = 8'h11;
            dest_arr[5] = 8'h11;
            dest_arr[6] = 8'h11;
            dest_arr[7] = 8'h11;
            dest_arr[8] = 8'h11;
            dest_arr[9] = 8'h11; 
            process_array_f = dest_arr[sel_func]; 
        end
    endfunction
    task automatic process_array_t;
        input logic [7:0] src_arr [9:0];
        output logic [7:0] dest_arr [9:0];
        begin
            dest_arr[0] = src_arr[0];
            dest_arr[1] = src_arr[1];
            dest_arr[2] = src_arr[2];
            dest_arr[3] = src_arr[3];
            dest_arr[4] = src_arr[4];
            dest_arr[5] = src_arr[5];
            dest_arr[6] = src_arr[6];
            dest_arr[7] = src_arr[7];
            dest_arr[8] = src_arr[8];
            dest_arr[9] = src_arr[9]; 
        end
    endtask
    always_comb begin
        func_result_out = process_array_f(input_val, local_array_f);
        output_val = local_array_f;
    end
    always_comb begin
        process_array_t(input_val, local_array_t);
        task_result_out = local_array_t[sel_func];
    end
endmodule
module module_wide_types_and_nested_arrays (
    input  logic [63:0] wide_data_scalar_in,
    input  logic [3:0]  addr_idx,
    output logic [63:0] wide_data_array_out [15:0],
    output logic [31:0] nested_mem_out      [3:0][3:0]
);
    logic [63:0] wide_temp_array [15:0];
    logic [31:0] nested_temp_mem [3:0][3:0];
    always_comb begin
        wide_temp_array[0]  = 64'hFEDCBA9876543210;
        wide_temp_array[1]  = 64'hFEDCBA9876543210;
        wide_temp_array[2]  = 64'hFEDCBA9876543210;
        wide_temp_array[3]  = 64'hFEDCBA9876543210;
        wide_temp_array[4]  = 64'hFEDCBA9876543210;
        wide_temp_array[5]  = 64'hFEDCBA9876543210;
        wide_temp_array[6]  = 64'hFEDCBA9876543210;
        wide_temp_array[7]  = 64'hFEDCBA9876543210;
        wide_temp_array[8]  = 64'hFEDCBA9876543210;
        wide_temp_array[9]  = 64'hFEDCBA9876543210;
        wide_temp_array[10] = 64'hFEDCBA9876543210;
        wide_temp_array[11] = 64'hFEDCBA9876543210;
        wide_temp_array[12] = 64'hFEDCBA9876543210;
        wide_temp_array[13] = 64'hFEDCBA9876543210;
        wide_temp_array[14] = 64'hFEDCBA9876543210;
        wide_data_array_out = wide_temp_array; 
        nested_temp_mem[0][0] = wide_data_scalar_in[31:0]; 
        nested_temp_mem[0][1] = wide_data_scalar_in[63:32];
        nested_temp_mem[0][2] = 32'hAAAA;
        nested_temp_mem[0][3] = 32'hBBBB;
        nested_temp_mem[1][0] = nested_temp_mem[0][0]; 
        nested_temp_mem[1][1] = nested_temp_mem[0][1]; 
        nested_temp_mem[1][2] = nested_temp_mem[0][2]; 
        nested_temp_mem[1][3] = nested_temp_mem[0][3]; 
        nested_temp_mem[2][0] = nested_temp_mem[1][0]; 
        nested_temp_mem[2][1] = nested_temp_mem[1][1];
        nested_temp_mem[2][2] = nested_temp_mem[1][2];
        nested_temp_mem[2][3] = nested_temp_mem[1][3];
        nested_temp_mem[3][0] = nested_temp_mem[2][0]; 
        nested_temp_mem[3][1] = nested_temp_mem[2][1];
        nested_temp_mem[3][2] = nested_temp_mem[2][2];
        nested_temp_mem[3][3] = nested_temp_mem[2][3]; 
        nested_mem_out = nested_temp_mem; 
    end
endmodule
