class MySimpleClass;
    int class_data;
    function new(int init_val);
        this.class_data = init_val;
    endfunction
    function int get_data();
        return class_data;
    endfunction
    function void set_data(int new_val);
        class_data = new_val;
    endfunction
endclass
module SampledBasic (
    input logic clk_i,
    input logic [7:0] data_in_i,
    output logic [7:0] data_sampled_o
);
    logic [7:0] internal_reg;
    logic [7:0] another_variable_for_scope;
    always_comb begin
        internal_reg = data_in_i + 1;
        another_variable_for_scope = 10;
        data_sampled_o = $sampled(internal_reg);
    end
endmodule
module SampledArithmetic (
    input logic clk_i,
    input int val_a_i,
    input int val_b_i,
    output int sum_sampled_o
);
    int intermediate_sum;
    int product_val;
    int difference_val;
    always_comb begin
        intermediate_sum = val_a_i + val_b_i;
        product_val = val_a_i * val_b_i;
        difference_val = val_a_i - val_b_i;
        sum_sampled_o = $sampled(intermediate_sum - product_val + difference_val);
    end
endmodule
module SampledArrayAccess (
    input logic clk_i,
    input logic [1:0] index_i,
    input logic [7:0] value_i,
    output logic [7:0] array_elem_sampled_o
);
    logic [7:0] my_array [0:3];
    logic [7:0] temp_array_element;
    always_comb begin
        for (int i = 0; i < 4; i++) begin
            my_array[i] = value_i + i;
        end
        temp_array_element = my_array[0];
        array_elem_sampled_o = $sampled(my_array[index_i]);
    end
endmodule
module SampledInFunction (
    input logic clk_i,
    input logic [15:0] input_val_i,
    output logic [15:0] processed_val_o
);
    logic [15:0] func_internal_var;
    function automatic logic [15:0] calculate_sampled_value(logic [15:0] arg_val);
        logic [15:0] temp_res;
        temp_res = arg_val * 2;
        return $sampled(temp_res + 5);
    endfunction
    always_comb begin
        func_internal_var = input_val_i;
        processed_val_o = calculate_sampled_value(func_internal_var);
    end
endmodule
module SampledWithStruct (
    input logic clk_i,
    input int data_x_i,
    input int data_y_i,
    output int sum_z_o
);
    typedef struct packed {
        int x;
        int y;
    } my_struct_t;
    my_struct_t my_data_s;
    int internal_z;
    always_comb begin
        my_data_s.x = data_x_i;
        my_data_s.y = data_y_i;
        internal_z = my_data_s.x + my_data_s.y;
        sum_z_o = $sampled(internal_z);
    end
endmodule
module SampledComplexLogic (
    input logic clk_i,
    input logic [3:0] in_a_i,
    input logic [3:0] in_b_i,
    input logic select_i,
    output logic [3:0] result_o
);
    logic [3:0] intermediate_val;
    always_comb begin
        if (select_i) begin
            intermediate_val = in_a_i + in_b_i;
            result_o = $sampled(intermediate_val);
        end else begin
            intermediate_val = in_a_i - in_b_i;
            result_o = $sampled(intermediate_val);
        end
    end
endmodule
module ModuleWithClass (
    input logic clk_i,
    input logic rst_n_i,
    input int initial_value_i,
    output int final_value_o
);
    MySimpleClass my_object_handle;
    int sampled_input_value_q;
    int processed_value_q;
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
            sampled_input_value_q <= 0;
            processed_value_q <= 0;
        end else begin
            sampled_input_value_q <= $sampled(initial_value_i);
            processed_value_q <= sampled_input_value_q + 5;
        end
    end
    assign final_value_o = processed_value_q;
endmodule
