module InnerVarMod (
    input wire clk,
    output logic [7:0] internal_data_out
);
    logic [7:0] m_internal_reg;
    always_ff @(posedge clk) begin
        m_internal_reg <= internal_data_out + 1; 
    end
    assign internal_data_out = m_internal_reg;
endmodule
module HierarchicalVarRefModule (
    input wire clk_i,
    input wire [7:0] data_in_i,
    output logic [7:0] result_o
);
    InnerVarMod inner_single (.clk(clk_i), .internal_data_out()); 
    task automatic modify_and_read_inner_var;
        input logic [7:0] new_val;
        begin
            inner_single.m_internal_reg = new_val; 
            result_o = inner_single.m_internal_reg + data_in_i; 
        end
    endtask
    always_comb begin
        modify_and_read_inner_var(data_in_i);
    end
endmodule
module InnerFuncMod (
    input wire req_i,
    output logic done_o
);
    logic internal_flag = 1'b0;
    task automatic perform_op (input int increment, output int current_val);
        internal_flag = !internal_flag; 
        current_val = increment + (internal_flag ? 1 : 0);
    endtask
    assign done_o = internal_flag;
endmodule
module HierarchicalFuncCallModule (
    input wire trigger_i,
    input int inc_val_i,
    output int current_sum_o
);
    InnerFuncMod inner_instance (.req_i(trigger_i), .done_o());
    int temp_sum;
    always_comb begin
        temp_sum = 0;
        if (trigger_i) begin
            inner_instance.perform_op(inc_val_i, temp_sum);
        end
        current_sum_o = temp_sum;
    end
endmodule
class MyClass;
    int m_data;
    function new(int init_val); 
        m_data = init_val;
    endfunction
    function int get_value(); 
        return m_data;
    endfunction
    function void set_value(int val); 
        m_data = val;
    endfunction
endclass
module ClassMethodNewModule (
    input wire clk_p,
    input int input_val_p,
    output int output_val_p
);
    MyClass my_obj;
    logic [7:0] dummy_count; 
    always_comb begin
        if (my_obj == null) begin
            my_obj = new(input_val_p); 
        end else begin
            my_obj.set_value(input_val_p); 
            output_val_p = my_obj.get_value() + dummy_count; 
        end
        dummy_count = (dummy_count + 1) % 256; 
    end
endmodule
module PublicFuncWrapperModule (
    input int func_in_i,
    output int func_out_o
);
    function automatic int get_data(int arg);
        return arg + 100;
    endfunction
    genvar i;
    for (i = 0; i < 2; i++) begin : named_gen_block
        function automatic int get_data(int arg);
            if (i == 0) return arg * 2;
            else return arg * 3;
        endfunction
    end
    task automatic calculate_all_funcs;
        input int val_t;
        output int res_t;
        int temp_res;
        begin
            temp_res = get_data(val_t); 
            temp_res += named_gen_block[0].get_data(val_t); 
            temp_res += named_gen_block[1].get_data(val_t); 
            res_t = temp_res;
        end
    endtask
    always_comb begin
        calculate_all_funcs(func_in_i, func_out_o);
    end
endmodule
module FuncLocalVarModule (
    input int data_x_i,
    input int data_y_i,
    output int result_z_o
);
    task automatic process_data_locally;
        input int val1;
        input int val2;
        int local_temp_sum;       
        logic [7:0] local_counter; 
        begin
            local_temp_sum = val1 + val2;             
            local_counter = (val1 % 10) + (val2 % 10); 
            result_z_o = local_temp_sum + local_counter;
        end
    endtask
    always_comb begin
        process_data_locally(data_x_i, data_y_i);
    end
endmodule
module ConstantPoolCandidateModule (
    input wire [3:0] multiplier_i,
    output wire [7:0] product_o
);
    parameter int CONST_FACTOR = 16;       
    localparam int OFFSET_VALUE = 5;       
    logic [7:0] intermediate_val;
    assign intermediate_val = multiplier_i * CONST_FACTOR; 
    assign product_o = intermediate_val + OFFSET_VALUE;    
    function automatic int calculate_with_constants(int input_val);
        localparam int MAGIC_NUMBER = 7; 
        return (input_val * MAGIC_NUMBER) + CONST_FACTOR;
    endfunction
    assign product_o = calculate_with_constants(multiplier_i) + product_o; 
endmodule
