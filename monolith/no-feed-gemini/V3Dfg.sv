module ArithmeticLogic (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    input logic       sel_op,
    output logic [8:0] out_arith_sum,
    output logic [7:0] out_bit_logic,
    output logic       out_comparison,
    output logic [7:0] out_conditional
);
    logic [7:0] temp_val1;
    logic [7:0] temp_val2;
    logic [7:0] temp_val3;
    logic [7:0] temp_val4;
    logic [7:0] temp_const_add;
    logic [7:0] temp_const_sub;
    logic [7:0] temp_const_mul;
    logic [7:0] temp_shift_left;
    logic [7:0] temp_shift_right;
    logic       temp_xor_comp;
    localparam int CONST_VAL_1 = 8'd10; 
    localparam int CONST_VAL_2 = 8'hAA; 
    assign temp_val1 = in_a + in_b; 
    assign temp_val2 = in_a - in_b; 
    assign temp_val3 = in_a * in_b; 
    assign temp_val4 = in_a / in_b; 
    assign out_arith_sum = temp_val1 + temp_val2 + temp_val3; 
    assign out_bit_logic = (in_a & in_b) | (~in_a ^ in_b); 
    assign temp_xor_comp = (in_a == in_b) ^ (in_a != in_b); 
    assign out_comparison = (in_a > CONST_VAL_1) && (in_b <= CONST_VAL_2); 
    assign temp_shift_left = in_a << 2; 
    assign temp_shift_right = in_b >> 1; 
    assign out_conditional = sel_op ? temp_shift_left : temp_shift_right; 
    assign temp_const_add = in_a + CONST_VAL_1;
    assign temp_const_sub = in_b - CONST_VAL_2;
    assign temp_const_mul = CONST_VAL_1 * CONST_VAL_2; 
    logic [7:0] common_expr;
    assign common_expr = (in_a + 3) & (in_b - 5);
    output logic [7:0] out_fanout1, out_fanout2, out_fanout3;
    assign out_fanout1 = common_expr;
    assign out_fanout2 = common_expr;
    assign out_fanout3 = common_expr; 
    output logic [15:0] out_long_const_add;
    assign out_long_const_add = {8'hF0, in_a} + 16'd12345;
endmodule
module BitSliceConcatenation (
    input logic [31:0] data_in,
    input logic [4:0]  index_lsb,
    input logic [4:0]  index_width_m1, 
    input logic [7:0]  array_in_val [4], 
    output logic       bit_sel_out,
    output logic [7:0] part_sel_out,
    output logic [63:0] packed_concat_out,
    output logic [7:0] unpacked_sum_out,
    output logic [7:0] array_elem_out 
);
    logic [31:0] internal_reg;
    logic [7:0]  temp_packed_arr [2]; 
    logic [7:0]  temp_unpacked_arr [4]; 
    logic [7:0]  local_arr_element;
    assign internal_reg = data_in; 
    assign bit_sel_out = internal_reg[index_lsb]; 
    assign part_sel_out = internal_reg[index_lsb +: (index_width_m1 + 1)]; 
    assign packed_concat_out = {data_in, data_in[7:0], internal_reg[31:16], 8'hCD}; 
    assign temp_unpacked_arr[0] = array_in_val[0];
    assign temp_unpacked_arr[1] = array_in_val[1];
    assign temp_unpacked_arr[2] = array_in_val[2] + 1;
    assign temp_unpacked_arr[3] = array_in_val[3]; 
    assign unpacked_sum_out = temp_unpacked_arr[0] + temp_unpacked_arr[1] + temp_unpacked_arr[2] + temp_unpacked_arr[3];
    assign array_elem_out = array_in_val[1];
    typedef struct packed {
        logic [3:0] field1;
        logic [3:0] field2;
    } my_packed_struct_t;
    my_packed_struct_t ps_in_val;
    output my_packed_struct_t ps_out;
    assign ps_in_val = {data_in[3:0], data_in[7:4]}; 
    assign ps_out = ps_in_val; 
    output logic [15:0] mixed_concat_out;
    assign mixed_concat_out = {ps_in_val.field1, 4'b0011, array_in_val[0][3:0], 4'b1100};
endmodule
module ProceduralControl (
    input logic [7:0] control_sel,
    input logic [7:0] data_val1,
    input logic [7:0] data_val2,
    input logic [7:0] data_val3,
    input logic [3:0] loop_limit_in,
    output logic [7:0] if_else_out,
    output logic [7:0] case_stmt_out,
    output logic [15:0] loop_sum_out,
    output logic [7:0] class_data_out,
    output logic [7:0] unique_case_out
);
    logic [7:0] internal_temp_if;
    logic [7:0] internal_temp_case;
    logic [15:0] sum_var;
    logic [7:0] temp_unique_case;
    class MyDataClass;
        logic [7:0] value;
        function new(logic [7:0] init_val);
            value = init_val;
        endfunction
        function logic [7:0] get_val();
            return value;
        endfunction
    endclass
    always_comb begin : comb_if_logic
        logic [7:0] local_if_var; 
        if (control_sel == 8'd0) begin
            internal_temp_if = data_val1;
            local_if_var = data_val1 + 1;
        end else if (control_sel == 8'd1) begin
            internal_temp_if = data_val2;
            local_if_var = data_val2 - 1;
        end else begin
            internal_temp_if = data_val3;
            local_if_var = data_val3 * 2;
        end
        if_else_out = internal_temp_if + local_if_var[7:0]; 
    end
    always_comb begin : comb_case_logic
        internal_temp_case = 8'b0;
        case (control_sel) 
            8'd0: internal_temp_case = data_val1 + 10;
            8'd1: internal_temp_case = data_val2 + 20;
            8'd2: internal_temp_case = data_val3 + 30;
            default: internal_temp_case = 8'hFF;
        endcase
        case_stmt_out = internal_temp_case;
    end
    always_comb begin : unique_case_block
        unique case (control_sel[1:0])
            2'b00: temp_unique_case = data_val1;
            2'b01: temp_unique_case = data_val2;
            2'b10: temp_unique_case = data_val3;
            2'b11: temp_unique_case = 8'hAB;
        endcase
        unique_case_out = temp_unique_case;
    end
    always_comb begin : comb_loop_logic
        sum_var = 16'b0;
        for (int i = 0; i < loop_limit_in; i++) begin 
            sum_var = sum_var + data_val1;
            logic [7:0] temp_in_loop = data_val2 + i; 
            sum_var = sum_var + temp_in_loop;
        end
        loop_sum_out = sum_var;
    end
    always_comb begin : class_inst_block
        MyDataClass my_object; 
        logic [7:0] local_class_val;
        if (control_sel[0]) begin
            my_object = new(data_val1); 
        end else begin
            my_object = new(data_val2);
        end
        local_class_val = my_object.get_val(); 
        class_data_out = local_class_val;
    end
endmodule
module DataTypesAndAlias (
    input logic [7:0] input_data_a,
    input logic [7:0] input_data_b,
    input logic [1:0] enum_sel,
    output logic [15:0] struct_field_out,
    output logic [7:0] enum_val_out,
    output logic [7:0] aliased_expr_out_1,
    output logic [7:0] aliased_expr_out_2,
    output logic [7:0] union_data_out
);
    typedef struct packed {
        logic [7:0] byte0;
        logic [7:0] byte1;
    } two_byte_t;
    typedef logic [3:0] nybble_array_t [2];
    two_byte_t my_struct_var; 
    nybble_array_t my_nybble_array; 
    typedef enum logic [1:0] {
        STATE_IDLE = 2'b00,
        STATE_ACTIVE = 2'b01,
        STATE_DONE = 2'b10
    } fsm_state_e;
    fsm_state_e current_state;
    typedef union {
        logic [7:0] byte_val;
        logic [3:0] nybble_val [2];
    } byte_nybble_u;
    byte_nybble_u my_union_var;
    always_comb begin
        my_struct_var.byte0 = input_data_a;
        my_struct_var.byte1 = input_data_b;
        struct_field_out = {my_struct_var.byte1, my_struct_var.byte0};
        my_nybble_array[0] = input_data_a[3:0];
        my_nybble_array[1] = input_data_b[3:0];
        current_state = fsm_state_e'(enum_sel); 
        case (current_state)
            STATE_IDLE: enum_val_out = 8'h11;
            STATE_ACTIVE: enum_val_out = 8'h22;
            STATE_DONE: enum_val_out = 8'h33;
            default: enum_val_out = 8'h00; 
        endcase
        logic [7:0] common_complex_expr;
        common_complex_expr = (input_data_a + input_data_b) ^ 8'h55; 
        aliased_expr_out_1 = common_complex_expr;
        aliased_expr_out_2 = common_complex_expr; 
        my_union_var.byte_val = input_data_a + 5;
        union_data_out = my_union_var.byte_val;
        my_union_var.nybble_val[0] = input_data_b[3:0];
        union_data_out = union_data_out + {my_union_var.nybble_val[1], 4'b0};
    end
endmodule
