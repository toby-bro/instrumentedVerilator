module UnpackedArraySimpleAssign_M1 (
    input logic [7:0] in_arr_m1[2],
    output logic [7:0] out_arr_m1[2]
);
    assign out_arr_m1 = in_arr_m1;
endmodule
module UnpackedArrayWithInitializer_M2 (
    input logic [7:0] val_m2,
    output logic [7:0] out_arr_m2[3]
);
    assign out_arr_m2 = '{val_m2, val_m2 + 1, val_m2 + 2};
endmodule
module UnpackedArrayConditionalAssign_M3 (
    input bit cond_m3,
    input logic [7:0] in_a_m3[2],
    input logic [7:0] in_b_m3[2],
    output logic [7:0] out_c_m3[2]
);
    assign out_c_m3 = cond_m3 ? in_a_m3 : in_b_m3;
endmodule
module UnpackedArrayEquality_M4 (
    input logic [7:0] in_x_m4[2],
    input logic [7:0] in_y_m4[2],
    output bit eq_res_m4,
    output bit neq_res_m4
);
    assign eq_res_m4 = (in_x_m4 == in_y_m4);
    assign neq_res_m4 = (in_x_m4 != in_y_m4);
endmodule
module UnpackedArrayCaseEquality_M5 (
    input logic [7:0] in_x_m5[2],
    input logic [7:0] in_y_m5[2],
    output bit eq_case_res_m5,
    output bit neq_case_res_m5
);
    assign eq_case_res_m5 = (in_x_m5 === in_y_m5);
    assign neq_case_res_m5 = (in_x_m5 !== in_y_m5);
endmodule
module UnpackedArraySlicing_M6 (
    input logic [7:0] full_arr_m6[4],
    output logic [7:0] sub_arr_out_m6[2]
);
    assign sub_arr_out_m6 = full_arr_m6[1+:2];
endmodule
module UnpackedStructAssign_M7 (
    input logic [7:0] val_a_m7,
    output logic [7:0] out_data_m7[2]
);
    typedef struct {
        logic [7:0] elements[2];
    } MyUnpackedStruct_t;
    MyUnpackedStruct_t in_struct_m7;
    MyUnpackedStruct_t out_struct_m7;
    assign in_struct_m7.elements = '{val_a_m7, val_a_m7 + 1};
    assign out_struct_m7 = in_struct_m7;
    assign out_data_m7 = out_struct_m7.elements;
endmodule
module UnpackedStructInitializer_M8 (
    input logic [7:0] val_a_m8,
    input logic [7:0] val_b_m8,
    output logic [7:0] out_arr_m8[2]
);
    typedef struct {
        logic [7:0] data_field[2];
    } StructWithUnpackedArr_t;
    StructWithUnpackedArr_t s_out_m8;
    assign s_out_m8 = '{ '{val_a_m8, val_b_m8} };
    assign out_arr_m8 = s_out_m8.data_field;
endmodule
module DynArrQueueLiteralAccess_M9 (
    input int base_val_m9,
    output int sum_val_m9
);
    int dyn_arr[];
    int q_var[$];
    int local_sum;
    always_comb begin
        dyn_arr = '{base_val_m9, base_val_m9 + 1, base_val_m9 + 2};
        q_var = '{base_val_m9 * 10, base_val_m9 * 11};
        local_sum = 0;
        if (dyn_arr.size() >= 1) begin
            local_sum += dyn_arr[0];
        end
        if (dyn_arr.size() >= 2) begin
            local_sum += dyn_arr[1];
        end
        if (q_var.size() >= 1) begin
            local_sum += q_var[0];
        end
    end
    assign sum_val_m9 = local_sum;
endmodule
module NestedAssignment_M10 (
    input int in_val_m10,
    output logic [7:0] out_arr_m10[2]
);
    logic [7:0] temp_val;
    always_comb begin
        out_arr_m10[0] = (temp_val = in_val_m10 + 5);
        out_arr_m10[1] = (temp_val + 1);
    end
endmodule
module PackedStructUnpackedArray_M11 (
    input logic [7:0] in_val_m11_0,
    input logic [7:0] in_val_m11_1,
    output logic [7:0] out_val_m11_0,
    output logic [7:0] out_val_m11_1
);
    typedef struct packed {
        logic [7:0] my_arr[2];
    } unpacked_struct_with_unpacked_array_t;
    unpacked_struct_with_unpacked_array_t in_s_m11;
    unpacked_struct_with_unpacked_array_t out_s_m11;
    assign in_s_m11.my_arr[0] = in_val_m11_0;
    assign in_s_m11.my_arr[1] = in_val_m11_1;
    assign out_s_m11 = in_s_m11;
    assign out_val_m11_0 = out_s_m11.my_arr[0];
    assign out_val_m11_1 = out_s_m11.my_arr[1];
endmodule
