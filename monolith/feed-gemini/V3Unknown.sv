module XConstantModule (
    input logic [7:0] in_x,
    output logic [7:0] out_x_and,
    output logic [7:0] out_x_or,
    output logic [7:0] out_const_assign
);
    logic [7:0] local_x_var;
    logic [7:0] another_x_var;
    always_comb begin
        local_x_var = 8'b1010_1X0Z;
        out_const_assign = local_x_var;
        out_x_and = in_x & 8'hF_X;
        out_x_or = in_x | 8'h0_Z;
        another_x_var = 8'b0011_X0X0;
    end
endmodule
module BitSelectBoundsModule (
    input logic [3:0] in_data,
    input int         in_bit_idx_rhs,
    input int         in_bit_idx_lhs,
    output logic      out_valid_bit,
    output logic [3:0] out_data_lhs_oob,
    output logic      out_oob_bit_rhs
);
    logic [2:0] my_vec;
    logic [3:0] my_array;
    assign my_vec = in_data[2:0];
    assign out_valid_bit = my_vec[1];
    assign out_oob_bit_rhs = in_data[in_bit_idx_rhs];
    always_comb begin
        my_array = 4'h0;
        my_array[in_bit_idx_lhs] = in_data[0];
    end
    assign out_data_lhs_oob = my_array;
endmodule
module ArraySelectBoundsModule (
    input logic [7:0] in_array_val,
    input int         in_array_idx,
    input int         in_multi_dim_idx,
    input int         in_string_array_idx,
    output logic [7:0] out_valid_array_element,
    output logic [7:0] out_oob_array_rhs,
    output logic [7:0] out_array_lhs_oob,
    output logic [3:0] out_mod_select,
    output logic [7:0] out_oob_multi_dim_rhs,
    output string     out_oob_string_rhs
);
    logic [7:0] my_fixed_array[2];
    logic [7:0] my_multi_dim_array[2][2];
    string my_string_array[2];
    always_comb begin
        my_fixed_array[0] = in_array_val + 1;
        my_fixed_array[1] = in_array_val + 2;
        my_multi_dim_array[0][0] = 8'h11;
        my_multi_dim_array[0][1] = 8'h22;
        my_multi_dim_array[1][0] = 8'h33;
        my_multi_dim_array[1][1] = 8'h44;
        my_string_array[0] = "hello";
        my_string_array[1] = "world";
        out_valid_array_element = my_fixed_array[0];
        out_oob_array_rhs = my_fixed_array[in_array_idx + 2];
        if (in_array_idx > 0) begin
            my_fixed_array[in_array_idx + 3] = in_array_val;
        end
        out_array_lhs_oob = my_fixed_array[0];
        out_oob_multi_dim_rhs = my_multi_dim_array[in_multi_dim_idx + 2][0];
        out_oob_string_rhs = my_string_array[in_string_array_idx + 2];
    end
    logic [3:0] mod_array[4];
    assign mod_array[0] = 4'b0001;
    assign mod_array[1] = 4'b0010;
    assign mod_array[2] = 4'b0100;
    assign mod_array[3] = 4'b1000;
    assign out_mod_select = mod_array[in_array_idx % 4];
endmodule
module WildcardAndUnknownModule (
    input logic [3:0] in_data_a,
    input logic [3:0] in_data_b,
    input logic [3:0] in_unknown_chk,
    output logic      out_eq_wild_match,
    output logic      out_neq_wild_no_match,
    output logic      out_is_unknown,
    output logic      out_eq_wild_non_const_rhs
);
    logic [3:0] four_state_var_rhs;
    assign four_state_var_rhs = in_data_a;
    assign out_eq_wild_match = (in_data_a ==? 4'b101X);
    assign out_neq_wild_no_match = (in_data_b !=? 4'b0Z01);
    assign out_is_unknown = $isunknown(in_unknown_chk);
    assign out_eq_wild_non_const_rhs = (in_data_a ==? four_state_var_rhs);
endmodule
module BitCountingModule (
    input logic [7:0] in_vector,
    output int        out_count_0,
    output int        out_count_1,
    output int        out_count_x,
    output int        out_count_z,
    output int        out_count_all_x_options
);
    logic [7:0] xz_vector = 8'b10X1Z0X1;
    assign out_count_0 = $countbits(in_vector, 1'b0);
    assign out_count_1 = $countbits(in_vector, 1'b1);
    assign out_count_x = $countbits(xz_vector, 1'bx);
    assign out_count_z = $countbits(xz_vector, 1'bz);
    assign out_count_all_x_options = $countbits(xz_vector, 1'bx, 1'bz, 1'bX);
endmodule
module CaseXModule (
    input logic [3:0] in_selector,
    output logic [3:0] out_case_val
);
    always_comb begin
        casez (in_selector)
            4'b101Z : out_case_val = 4'b0001;
            4'bX010 : out_case_val = 4'b0010;
            default : out_case_val = 4'b1111;
        endcase
    end
endmodule
module ClassParamContainerModule (
    input logic in_trigger,
    output logic out_status
);
    parameter int PARAM_VAL = 10;
    class MySimpleClass;
        logic [7:0] class_data;
        function new();
            class_data = 8'hAA;
        endfunction
    endclass
    MySimpleClass my_class_inst;
    always_comb begin
        if (in_trigger) begin
            my_class_inst = new();
            out_status = my_class_inst.class_data[0];
        end else begin
            out_status = 1'b0;
        end
        out_status = out_status || (PARAM_VAL == 10);
    end
endmodule
