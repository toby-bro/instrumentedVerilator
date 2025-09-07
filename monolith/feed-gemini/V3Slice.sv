module SliceAssignModule (
    input logic [3:0] in_idx,
    input logic [7:0] in_val,
    input logic [7:0] in_val2,
    input logic in_cond,
    output logic [7:0] out_unpacked_arr [0:3],
    output logic [7:0] out_packed_arr,
    output logic [7:0] out_struct_arr_member [0:3]
);
    typedef struct {
        logic [7:0] data_packed_internal;
        logic [7:0] data_unpacked [0:3];
    } MyStruct;
    MyStruct s_inst;
    logic [7:0] unpacked_arr_in [0:3];
    logic [7:0] packed_arr_in;
    logic [7:0] temp_val_for_expr;
    always_comb begin
        unpacked_arr_in = '{in_val, in_val + 1, in_val + 2, in_val + 3};
        s_inst.data_unpacked = '{in_val2, in_val2 + 1, in_val2 + 2, in_val2 + 3};
        packed_arr_in = in_val + 10;
        if (in_idx < 4) begin
            unpacked_arr_in[in_idx] = packed_arr_in;
        end
        out_unpacked_arr = in_cond ? unpacked_arr_in : s_inst.data_unpacked;
        temp_val_for_expr = (in_val * 3) / 2;
        out_packed_arr = temp_val_for_expr[7:0];
        out_struct_arr_member = s_inst.data_unpacked;
    end
endmodule
module ArrayComparisonModule (
    input logic [7:0] array_a [0:2],
    input logic [7:0] array_b [0:2],
    input logic [7:0] array_c [0:2],
    output logic       out_eq,
    output logic       out_neq,
    output logic       out_eq_case,
    output logic       out_neq_case
);
    always_comb begin
        out_eq = (array_a == array_b);
        out_neq = (array_a != array_b);
        out_eq_case = (array_a === array_c);
        out_neq_case = (array_a !== array_c);
    end
endmodule
module InitializerConstructorModule (
    input logic [7:0] in_data_init,
    input logic [7:0] in_data_dyn,
    input logic [7:0] in_data_q,
    output logic [7:0] out_fixed_arr [0:3],
    output logic [7:0] out_dyn_arr_val,
    output logic [7:0] out_q_val,
    output logic [15:0] out_packed_struct_val
);
    typedef struct packed {
        logic [7:0] field1;
        logic [7:0] field2;
    } PackedStruct;
    typedef struct {
        int id;
        logic [7:0] data_unp [0:1];
    } UnpackedStruct;
    logic [7:0] fixed_array_internal [0:3];
    logic [7:0] dynamic_array [];
    logic [7:0] queue_var [$];
    PackedStruct p_struct_var;
    UnpackedStruct u_struct_var;
    always_comb begin
        fixed_array_internal = '{in_data_init, in_data_init + 1, in_data_init + 2, in_data_init + 3};
        out_fixed_arr = fixed_array_internal;
        dynamic_array = new[2];
        if (dynamic_array.size() == 2) begin
            dynamic_array[0] = in_data_dyn;
            dynamic_array[1] = in_data_dyn + 1;
            out_dyn_arr_val = dynamic_array[0];
        end else begin
            out_dyn_arr_val = '0;
        end
        queue_var = {};
        queue_var.push_back(in_data_q);
        queue_var.push_back(in_data_q + 1);
        if (queue_var.size() > 0) begin
            out_q_val = queue_var.pop_front();
        end else begin
            out_q_val = '0;
        end
        p_struct_var = '{field1: in_data_init + 4, field2: in_data_init + 5};
        out_packed_struct_val = p_struct_var.field1 | (p_struct_var.field2 << 8);
        u_struct_var.id = in_data_init + 6;
        u_struct_var.data_unp = '{in_data_init + 7, in_data_init + 8};
    end
endmodule
module SliceSelectionModule (
    input logic [31:0] in_large_val,
    input logic [7:0] in_arr_data [0:3],
    input int in_index,
    output logic [7:0] out_part1,
    output logic [7:0] out_part2,
    output logic [7:0] out_array_elem,
    output logic [7:0] out_slice_of_array_elem
);
    logic [31:0] internal_reg;
    logic [7:0] internal_unpacked_arr [0:3];
    always_comb begin
        internal_reg = in_large_val;
        internal_unpacked_arr = in_arr_data;
        out_part1 = internal_reg[7:0];
        if (in_index >= 0 && (in_index + 7) < 32) begin
            out_part2 = internal_reg[in_index +: 8];
        end else begin
            out_part2 = '0;
        end
        if (in_index >= 0 && in_index < 4) begin
            out_array_elem = internal_unpacked_arr[in_index];
        end else begin
            out_array_elem = '0;
        end
        out_slice_of_array_elem = internal_unpacked_arr[0][7:0];
    end
endmodule
module StructMemberAccessModule (
    input int             in_scalar,
    input logic [7:0]     in_struct_data [0:1],
    output logic [7:0]    out_member_data,
    output logic          out_func_result
);
    typedef struct {
        int               id_field;
        logic [7:0]       data_field [0:1];
    } ComplexStruct;
    ComplexStruct my_complex_struct;
    class MyClass;
        int value;
        function new(int v);
            value = v;
        endfunction
        function automatic logic get_bool_val();
            return (value > 0);
        endfunction
    endclass
    MyClass my_object;
    always_comb begin
        my_object = new(in_scalar);
        my_complex_struct.id_field = in_scalar;
        my_complex_struct.data_field = in_struct_data;
        out_member_data = my_complex_struct.data_field[0];
        out_func_result = my_object.get_bool_val();
    end
endmodule
