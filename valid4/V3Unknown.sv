typedef struct packed {
    logic [7:0] field1;
    logic [7:0] field2;
    logic [7:0] field3_x;
} my_struct_t;
module ContinuousAssignDynamicSelects (
    input  logic [3:0] in_vec,
    input  logic [2:0] idx_in,
    input  logic [2:0] part_msb,
    input  logic [2:0] part_lsb,
    input  logic [7:0] input_val,
    output logic [7:0] out_val_x,
    output logic        out_read_sel,
    output logic [3:0] out_read_partsel,
    output logic [3:0] out_write_target,
    output logic [7:0] out_partsel_write_target
);
    logic [7:0] internal_x_val;
    logic [3:0] target_wire;
    logic [7:0] target_partsel_wire;
    assign internal_x_val = 8'h5x;
    assign out_val_x = internal_x_val;
    assign out_read_sel = in_vec[idx_in];
    assign out_read_partsel = in_vec[part_lsb +: (part_msb - part_lsb + 1)];
    assign target_wire[idx_in] = input_val[3:0];
    assign out_write_target = target_wire;
    assign target_partsel_wire[part_lsb +: (part_msb - part_lsb + 1)] = input_val[0 +: (part_msb - part_lsb + 1)];
    assign out_partsel_write_target = target_partsel_wire;
endmodule
module ProceduralAssignDynamicSelects (
    input  logic        clk,
    input  logic [7:0]  in_array_idx,
    input  logic [3:0]  in_data_val,
    input  logic [7:0]  out_of_bounds_idx,
    output logic [3:0]  out_array_read_val,
    output logic [3:0]  out_lvalue_modified [0:3],
    output logic [3:0]  out_default_val_read,
    output logic [7:0]  out_reg_bit_write,
    output logic [7:0]  out_reg_part_write,
    output logic [3:0]  out_struct_array_read_val
);
    logic [3:0] local_array [0:3];
    logic [7:0] my_reg_bit_target;
    logic [7:0] my_reg_part_target;
    typedef struct {
        logic [3:0] inner_array [0:3];
    } inner_struct_t;
    inner_struct_t outer_struct_array [0:1];
    always_comb begin
        for (int i = 0; i < 4; i++) begin
            local_array[i] = {4{1'b0}};
        end
        for (int i = 0; i < 2; i++) begin
            for (int j = 0; j < 4; j++) begin
                outer_struct_array[i].inner_array[j] = {4{1'b0}};
            end
        end
        my_reg_bit_target = 8'h1X;
    end
    assign out_array_read_val = local_array[in_array_idx];
    assign out_default_val_read = local_array[out_of_bounds_idx];
    always_comb begin
        local_array[out_of_bounds_idx] = in_data_val;
    end
    always_ff @(posedge clk) begin
        my_reg_bit_target[in_array_idx] <= in_data_val[0];
        my_reg_part_target[7:0] <= in_data_val[3:0] + 4'hA;
    end
    always_ff @(posedge clk) begin
        outer_struct_array[in_array_idx].inner_array[out_of_bounds_idx] <= 4'h5;
    end
    assign out_struct_array_read_val = outer_struct_array[in_array_idx].inner_array[in_data_val];
    genvar i;
    for (i = 0; i < 4; i++) begin : gen_lvalue_out_array
        assign out_lvalue_modified[i] = local_array[i];
    end
    assign out_reg_bit_write = my_reg_bit_target;
    assign out_reg_part_write = my_reg_part_target;
endmodule
module CaseAndEqualityOperators (
    input  logic [3:0] in_a,
    input  logic [3:0] in_b,
    input  logic [3:0] in_val,
    input  logic [3:0] dynamic_rhs,
    output logic        out_casez_res,
    output logic        out_casex_res,
    output logic        out_eqcase_res,
    output logic        out_neqcase_res,
    output logic        out_eqwild_res,
    output logic        out_neqwild_res
);
    logic [3:0] x_const = 4'b1x0z;
    logic [3:0] z_const = 4'b0z1x;
    always_comb begin
        casez (in_val)
            4'b1x0z: out_casez_res = 1'b1;
            default: out_casez_res = 1'b0;
        endcase
        casex (in_val)
            4'b0z1x: out_casex_res = 1'b1;
            default: out_casex_res = 1'b0;
        endcase
    end
    assign out_eqcase_res  = (in_a === 4'b10xz);
    assign out_neqcase_res = (in_b !== 4'b0x1x);
    assign out_eqwild_res  = (in_a ==? dynamic_rhs);
    assign out_neqwild_res = (in_b !=? dynamic_rhs);
endmodule
module IsUnknownAndCountBits (
    input  logic [7:0] input_data,
    input  logic [7:0] input_non_x_val,
    input  logic [7:0] input_some_x_val,
    input  logic [7:0] input_dynamic_val,
    output logic        isunknown_result,
    output logic [3:0] countbits_all_x_res,
    output logic [3:0] countbits_mixed_res_1,
    output logic [3:0] countbits_mixed_res_2
);
    logic [7:0] const_x_val = 8'b1010_xxxx;
    logic [7:0] const_z_val = 8'b0101_zzzz;
    logic [7:0] const_all_x_z = 8'b11xx_00zz;
    assign isunknown_result = $isunknown(input_data);
    assign countbits_all_x_res = $countbits(const_x_val, const_z_val, const_all_x_z);
    assign countbits_mixed_res_1 = $countbits(const_x_val, const_z_val, input_dynamic_val);
    assign countbits_mixed_res_2 = $countbits(input_some_x_val, input_non_x_val, const_x_val);
endmodule
module NonBlockingAssignmentsAndParameters (
    input  logic        clk,
    input  logic [7:0] in_d_val,
    output logic [7:0] out_q_reg,
    output logic        out_param_check
);
    logic [7:0] q_reg;
    always_ff @(posedge clk) begin
        q_reg <= in_d_val;
    end
    assign out_q_reg = q_reg;
    parameter int MY_PARAM = 10;
    localparam logic [3:0] CONST_VAL_PARAM = 4'b1x01;
    assign out_param_check = (MY_PARAM > 0);
endmodule
class MyClass;
    logic [15:0] data;
    logic [7:0] internal_temp_val;
    function new();
        data = 16'hZZXX;
    endfunction
    task set_data(logic [15:0] val);
        data = val;
    endtask
    function logic [7:0] get_internal_temp_val();
        internal_temp_val = 8'b1010_1010;
        return internal_temp_val;
    endfunction
endclass
module StructuresAndClasses (
    input  my_struct_t   in_struct_data,
    input  logic [15:0]  in_class_val_a,
    input  logic [15:0]  in_class_val_b,
    output logic [15:0]  out_struct_sum,
    output logic [15:0]  out_class_data,
    output logic [7:0]   out_class_internal_val
);
    MyClass my_instance_1;
    MyClass my_instance_2;
    logic [7:0] temp_class_method_output_val;
    assign out_struct_sum = in_struct_data.field1 + in_struct_data.field2 + in_struct_data.field3_x;
    always_comb begin
        if (my_instance_1 == null) begin
            my_instance_1 = new();
        end
        if (my_instance_2 == null) begin
            my_instance_2 = new();
        end
        my_instance_1.set_data(in_class_val_a);
        my_instance_2.set_data(in_class_val_b);
        out_class_data = my_instance_1.data + my_instance_2.data;
        temp_class_method_output_val = my_instance_1.get_internal_temp_val();
    end
    assign out_class_internal_val = temp_class_method_output_val;
endmodule
