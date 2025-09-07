module mod_unpacked_array_assign (
    input logic [7:0] in_data_a,
    output logic [7:0] out_data_a
);
    logic [7:0] unpacked_arr_l [4];
    logic [7:0] unpacked_arr_r [4];
    logic [7:0] unpacked_arr_single_elem;
    logic [7:0] packed_arr_l;
    logic [7:0] packed_arr_r;
    always_comb begin
        for (int i = 0; i < 4; i++) begin
            unpacked_arr_l[i] = in_data_a + i;
        end
        unpacked_arr_r = unpacked_arr_l; 
        unpacked_arr_single_elem = unpacked_arr_l[2];
        packed_arr_l = in_data_a;
        packed_arr_r = packed_arr_l;
        if (in_data_a[0]) begin
            unpacked_arr_l[0] = in_data_a;
        end else begin
            unpacked_arr_l[0] = in_data_a + 1;
        end
        out_data_a = unpacked_arr_r[0] + unpacked_arr_single_elem + packed_arr_r + unpacked_arr_l[0];
    end
endmodule
module mod_unpacked_array_comp (
    input logic [3:0] in_val_a,
    input logic [3:0] in_val_b,
    output logic out_eq,
    output logic out_neq,
    output logic out_eq_case,
    output logic out_neq_case
);
    logic [3:0] arr1 [2];
    logic [3:0] arr2 [2];
    logic [3:0] arr3 [2];
    logic [3:0] arr4 [2];
    always_comb begin
        arr1[0] = in_val_a;
        arr1[1] = in_val_a + 1;
        arr2[0] = in_val_b;
        arr2[1] = in_val_b + 1;
        arr3[0] = in_val_a;
        arr3[1] = in_val_a + 1;
        arr4[0] = 4'b0Z; 
        arr4[1] = 4'bX0;
        out_eq = (arr1 == arr2);
        out_neq = (arr1 != arr3);
        out_eq_case = (arr1 === arr4);
        out_neq_case = (arr1 !== arr2);
    end
endmodule
module mod_array_init_assign (
    input logic [1:0] in_idx,
    input logic [1:0] in_val,
    output logic [1:0] out_arr_elem
);
    logic [1:0] fixed_arr [3] = {2'd1, 2'd2, 2'd3}; 
    logic [1:0] temp_arr [3];
    logic [1:0] result_arr [3];
    logic [1:0] assign_val;
    always_comb begin
        temp_arr = fixed_arr;
        assign_val = in_val;
        result_arr[in_idx] = assign_val;
        result_arr = {in_val, in_val + 1, in_val + 2};
        out_arr_elem = result_arr[in_idx] + temp_arr[in_idx];
    end
endmodule
module mod_struct_array_assign (
    input logic [7:0] in_sval_a,
    input logic [7:0] in_sval_b,
    output logic [7:0] out_sdata
);
    typedef struct packed {
        logic [3:0] field1;
        logic [3:0] field2;
    } my_packed_struct_t;
    typedef struct {
        logic [7:0] data;
        my_packed_struct_t p_data;
    } my_unpacked_struct_t;
    my_unpacked_struct_t struct_arr [2]; 
    always_comb begin
        struct_arr[0].data = in_sval_a;
        struct_arr[0].p_data.field1 = in_sval_a[3:0];
        struct_arr[0].p_data.field2 = in_sval_a[7:4];
        struct_arr[1].data = in_sval_b;
        struct_arr[1].p_data.field1 = in_sval_b[3:0];
        struct_arr[1].p_data.field2 = in_sval_b[7:4];
        struct_arr[0] = struct_arr[1];
        out_sdata = struct_arr[0].data + struct_arr[0].p_data.field1;
    end
endmodule
module mod_slice_sel_assign (
    input logic [7:0] in_slice_data,
    output logic [7:0] out_slice_result
);
    logic [7:0] multi_dim_arr [2][3]; 
    logic [7:0] row_slice [3];
    always_comb begin
        for (int i = 0; i < 2; i++) begin
            for (int j = 0; j < 3; j++) begin
                multi_dim_arr[i][j] = in_slice_data + i + j;
            end
        end
        row_slice = multi_dim_arr[0];
        multi_dim_arr[1] = {in_slice_data, in_slice_data + 1, in_slice_data + 2};
        out_slice_result = row_slice[1] + multi_dim_arr[1][2];
    end
endmodule
module mod_dynamic_array_ops (
    input logic [7:0] in_dyn_data,
    output logic [7:0] out_dyn_sum
);
    logic [7:0] dynamic_arr [];
    logic [7:0] sum;
    always_comb begin
        sum = 0;
        dynamic_arr = new [4];
        for (int i = 0; i < dynamic_arr.size(); i++) begin
            dynamic_arr[i] = in_dyn_data + i;
        end
        dynamic_arr = new [dynamic_arr.size() + 1] (dynamic_arr);
        dynamic_arr[dynamic_arr.size() - 1] = in_dyn_data + 10;
        foreach (dynamic_arr[idx]) begin
            sum = sum + dynamic_arr[idx];
        end
        if (dynamic_arr.size() > 2) dynamic_arr.delete(2, 1); 
        dynamic_arr.delete(); 
        dynamic_arr = new [1];
        if (!dynamic_arr.size()) begin 
            dynamic_arr = new [1] (dynamic_arr);
        end
        dynamic_arr[0] = in_dyn_data;
        sum = dynamic_arr[0];
        out_dyn_sum = sum;
    end
endmodule
module mod_queue_ops (
    input logic [7:0] in_q_data,
    output logic [7:0] out_q_sum
);
    logic [7:0] my_queue [$];
    logic [7:0] sum;
    logic [7:0] temp_val;
    always_comb begin
        sum = 0;
        my_queue = {};
        my_queue.push_back(in_q_data);
        my_queue.push_front(in_q_data + 1);
        my_queue.push_back(in_q_data + 2);
        if (my_queue.size() > 0) begin
            temp_val = my_queue.pop_front();
            sum = sum + temp_val;
            if (my_queue.size() > 0) begin
                temp_val = my_queue.pop_back();
                sum = sum + temp_val;
            end
        end
        foreach (my_queue[idx]) begin
            sum = sum + my_queue[idx];
        end
        if (my_queue.size() > 0) begin
            my_queue.delete(0);
        end
        my_queue.push_back(in_q_data + 5);
        my_queue.push_back(in_q_data + 6);
        sum = 0;
        foreach (my_queue[idx]) begin
            sum = sum + my_queue[idx];
        end
        out_q_sum = sum;
    end
endmodule
module mod_packed_array_struct_assign (
    input logic [7:0] in_ps_data,
    output logic [7:0] out_ps_data
);
    typedef struct packed {
        logic [3:0] f1;
        logic [3:0] f2;
    } packed_s;
    packed_s ps_arr [2]; 
    packed_s single_ps;
    logic [15:0] full_packed_val; 
    always_comb begin
        ps_arr[0].f1 = in_ps_data[3:0];
        ps_arr[0].f2 = in_ps_data[7:4];
        ps_arr[1].f1 = in_ps_data[0] ? 4'hA : 4'hB;
        ps_arr[1].f2 = in_ps_data[1] ? 4'hC : 4'hD;
        single_ps = ps_arr[0];
        full_packed_val = {in_ps_data, in_ps_data + 1};
        out_ps_data = single_ps.f1 + single_ps.f2 + ps_arr[1].f1 + ps_arr[1].f2 + full_packed_val[7:0];
    end
endmodule
module mod_class_and_method_hard (
    input logic in_cl_val,
    output int out_cl_res
);
    class MyClass;
        rand int m_field;
        logic [7:0] my_unpacked_data [3]; 
        function new();
            m_field = 10;
            my_unpacked_data[0] = 1;
            my_unpacked_data[1] = 2;
            my_unpacked_data[2] = 3;
        endfunction
        function int calculate(int val);
            return m_field + val;
        endfunction
        function logic [7:0] get_unpacked_array_element(int idx);
            return my_unpacked_data[idx];
        endfunction
        function logic [7:0][2:0] get_whole_unpacked_array(); 
            return {my_unpacked_data[0], my_unpacked_data[1], my_unpacked_data[2]};
        endfunction
        function logic [7:0] get_single_unpacked_slice(int start_idx); 
            return my_unpacked_data[start_idx];
        endfunction
    endclass
    MyClass my_object;
    int temp_res;
    logic [7:0] extracted_element;
    logic [7:0][2:0] returned_packed_array; 
    always_comb begin
        if (my_object == null) begin
            my_object = new(); 
        end
        temp_res = my_object.calculate(in_cl_val ? 5 : 10);
        temp_res = temp_res + my_object.m_field;
        extracted_element = my_object.get_unpacked_array_element(1);
        temp_res = temp_res + extracted_element;
        returned_packed_array = my_object.get_whole_unpacked_array();
        extracted_element = returned_packed_array[7:0]; 
        temp_res = temp_res + extracted_element;
        temp_res = temp_res + $bits(my_object.m_field);
        temp_res = temp_res + $clog2(temp_res);
        out_cl_res = temp_res;
    end
endmodule
module mod_expr_stmt (
    input logic [7:0] in_es_val,
    output logic [7:0] out_es_val
);
    logic [7:0] internal_reg [3];
    logic [7:0] temp_val;
    function logic [7:0] update_and_get(logic [7:0] val);
        internal_reg[0] = val + 1; 
        return internal_reg[0] + 5;
    endfunction
    function void set_internal(logic [7:0] val);
        internal_reg[1] = val + 2;
    endfunction
    always_comb begin
        internal_reg[0] = 0;
        internal_reg[1] = 0;
        internal_reg[2] = 0;
        temp_val = update_and_get(in_es_val);
        internal_reg[2] = temp_val;
        set_internal(in_es_val + 3);
        if (in_es_val[0]) begin
            internal_reg[0] = update_and_get(in_es_val);
        end else begin
            internal_reg[0] = in_es_val + 10;
        end
        out_es_val = internal_reg[0] + internal_reg[1] + internal_reg[2];
    end
endmodule
