module BasicArithmeticLogicAndComparisons #(parameter int P_WIDTH = 8) (
    input logic [P_WIDTH-1:0] in_a,
    input logic [P_WIDTH-1:0] in_b,
    input int                 in_val_s,
    input logic               in_bit_c,
    output logic [P_WIDTH-1:0] out_expr_zero_ones_simplify,
    output logic [P_WIDTH-1:0] out_expr_same_operands,
    output bit                 out_comp_signed_zero,
    output bit                 out_comp_unsigned_ones,
    output bit                 out_comp_swap_sides
);
    assign out_expr_zero_ones_simplify = (P_WIDTH'(0)) + in_a; 
    assign out_expr_zero_ones_simplify = in_a + (P_WIDTH'(0)); 
    assign out_expr_zero_ones_simplify = (P_WIDTH'(0)) & in_a; 
    assign out_expr_zero_ones_simplify = in_a & (P_WIDTH'(0)); 
    assign out_expr_zero_ones_simplify = (P_WIDTH'(-1)) & in_a; 
    assign out_expr_zero_ones_simplify = in_a & (P_WIDTH'(-1)); 
    assign out_expr_zero_ones_simplify = (P_WIDTH'(0)) | in_a; 
    assign out_expr_zero_ones_simplify = in_a | (P_WIDTH'(0)); 
    assign out_expr_zero_ones_simplify = (P_WIDTH'(-1)) | in_a; 
    assign out_expr_zero_ones_simplify = in_a | (P_WIDTH'(-1)); 
    assign out_expr_zero_ones_simplify = (P_WIDTH'(0)) ^ in_a; 
    assign out_expr_zero_ones_simplify = in_a ^ (P_WIDTH'(0)); 
    assign out_expr_zero_ones_simplify = (P_WIDTH'(-1)) ^ in_a; 
    assign out_expr_same_operands = in_a & in_a; 
    assign out_expr_same_operands = in_a | in_a; 
    assign out_expr_same_operands = in_a ^ in_a; 
    assign out_comp_signed_zero = (in_val_s == in_val_s); 
    assign out_comp_signed_zero = (in_val_s != in_val_s); 
    assign out_comp_signed_zero = (in_val_s > in_val_s);  
    assign out_comp_signed_zero = (in_val_s < in_val_s);  
    assign out_comp_signed_zero = (in_val_s >= in_val_s); 
    assign out_comp_signed_zero = (in_val_s <= in_val_s); 
    assign out_comp_signed_zero = (32'd0 > in_val_s);   
    assign out_comp_signed_zero = (in_val_s >= 32'd0); 
    assign out_comp_signed_zero = (in_val_s < 32'd0);   
    assign out_comp_signed_zero = (32'd0 <= in_val_s);  
    assign out_comp_unsigned_ones = (in_a > {P_WIDTH{1'b1}});   
    assign out_comp_unsigned_ones = ({P_WIDTH{1'b1}} < in_a);   
    assign out_comp_unsigned_ones = ({P_WIDTH{1'b1}} >= in_a);  
    assign out_comp_unsigned_ones = (in_a <= {P_WIDTH{1'b1}});  
    assign out_comp_swap_sides = (in_val_s > 10); 
    assign out_comp_swap_sides = (5 < in_val_s);  
endmodule
module ShiftAndPowerOfTwoOptimizations #(parameter int P_DATA_WIDTH = 32) (
    input logic [P_DATA_WIDTH-1:0] in_data,
    input longint                  in_shift_amount, 
    output logic [P_DATA_WIDTH-1:0] out_shifted_data
);
    assign out_shifted_data = (P_DATA_WIDTH'(0)) << in_data[4:0]; 
    assign out_shifted_data = in_data << (P_DATA_WIDTH'(0));     
    assign out_shifted_data = (P_DATA_WIDTH'(0)) >> in_data[4:0]; 
    assign out_shifted_data = in_data >> (P_DATA_WIDTH'(0));     
    assign out_shifted_data = in_data << in_shift_amount; 
    assign out_shifted_data = in_data >> in_shift_amount; 
    assign out_shifted_data = in_data / P_DATA_WIDTH'(4);  
    assign out_shifted_data = P_DATA_WIDTH'(8) * in_data; 
    assign out_shifted_data = in_data % P_DATA_WIDTH'(16); 
    assign out_shifted_data = 2 ** in_data[4:0]; 
    assign out_shifted_data = (in_data & (in_data + 1)) << 2; 
    assign out_shifted_data = (in_data | (in_data - 1)) >> 2; 
    assign out_shifted_data = (in_data << 3) << 5;           
    assign out_shifted_data = (in_data >> 2) >> 4;           
    assign out_shifted_data = (in_data << 1) | (in_data << 1); 
    assign out_shifted_data = (in_data >> 1) ^ (in_data >> 1); 
endmodule
module ConditionalAndLogicalOps #(parameter int P_COND_WIDTH = 1, parameter int P_DATA_WIDTH = 8) (
    input logic [P_COND_WIDTH-1:0] in_cond_a,
    input logic [P_COND_WIDTH-1:0] in_cond_b,
    input logic [P_DATA_WIDTH-1:0] in_data_x,
    input logic [P_DATA_WIDTH-1:0] in_data_y,
    output logic [P_DATA_WIDTH-1:0] out_cond_result,
    output logic [P_COND_WIDTH-1:0] out_logical_simplify
);
    assign out_cond_result = (P_COND_WIDTH'(0)) ? in_data_x : in_data_y; 
    assign out_cond_result = (P_COND_WIDTH'(1)) ? in_data_x : in_data_y; 
    assign out_cond_result = in_cond_a ? in_data_x : in_data_x;       
    assign out_cond_result = !in_cond_a ? in_data_x : in_data_y;      
    assign out_logical_simplify = in_cond_a ? (P_COND_WIDTH'(1)) : in_cond_b; 
    assign out_logical_simplify = in_cond_a ? in_cond_b : (P_COND_WIDTH'(0));   
    assign out_logical_simplify = in_cond_a ? in_cond_b : (P_COND_WIDTH'(1)); 
    assign out_logical_simplify = in_cond_a ? (P_COND_WIDTH'(0)) : in_cond_b;   
    assign out_logical_simplify = in_cond_a && in_cond_b; 
    assign out_logical_simplify = in_cond_a || in_cond_b; 
    assign out_logical_simplify = !(in_cond_a); 
    assign out_cond_result = (P_DATA_WIDTH'(-1)) & (in_data_x == in_data_y); 
    assign out_cond_result = (P_DATA_WIDTH'(-1)) & (in_cond_a ? in_data_x : in_data_y); 
    assign out_cond_result = (P_DATA_WIDTH'h0F) & ((in_data_x << 8) | (in_data_y >> 4)); 
    assign out_cond_result = (P_DATA_WIDTH'hFF) & (in_data_x >> 0); 
    assign out_cond_result = (P_DATA_WIDTH'hF0) & (in_data_x << 4); 
    assign out_logical_simplify = in_cond_a || (!in_cond_a && in_cond_b); 
    assign out_logical_simplify = (in_cond_a == in_cond_b);
endmodule
module DataStructuringOptimizations #(parameter int P_BUS_WIDTH = 8) (
    input logic [P_BUS_WIDTH-1:0] in_val_1,
    input logic [P_BUS_WIDTH-1:0] in_val_2,
    input logic [P_BUS_WIDTH-1:0] in_val_3,
    input logic [P_BUS_WIDTH-1:0] in_val_4,
    input logic [P_BUS_WIDTH*2-1:0] in_packed_wide_data,
    output logic [P_BUS_WIDTH-1:0] out_concat_simplify,
    output logic [P_BUS_WIDTH-1:0] out_select_simplify,
    output logic out_reduction_simplify
);
    assign out_concat_simplify = {P_BUS_WIDTH'(0), in_val_1}; 
    assign out_concat_simplify = {in_packed_wide_data[P_BUS_WIDTH*2-1:P_BUS_WIDTH], in_packed_wide_data[P_BUS_WIDTH-1:0]};
    assign out_concat_simplify = {(in_val_1 & in_val_2), (in_val_3 & in_val_4)}; 
    assign out_concat_simplify = {in_val_1 & in_val_2[0], in_val_1 & in_val_2[1]}; 
    assign out_concat_simplify = {in_val_1, in_val_1};
    assign out_concat_simplify = {{2{in_val_1}}, in_val_1}; 
    assign out_concat_simplify = {in_val_1, {2{in_val_1}}}; 
    assign out_concat_simplify = {2{ {2{in_val_1}} }}; 
    assign out_select_simplify = in_val_1[P_BUS_WIDTH-1:0]; 
    assign out_select_simplify = in_val_1[P_BUS_WIDTH-1:0]; 
    assign out_select_simplify = in_packed_wide_data[P_BUS_WIDTH+P_BUS_WIDTH/2-1 : P_BUS_WIDTH/2][P_BUS_WIDTH/4-1 : 0]; 
    assign out_select_simplify = (in_val_1 + in_val_2)[P_BUS_WIDTH-1:0]; 
    assign out_select_simplify = (in_val_1 & in_val_2)[P_BUS_WIDTH-1:0]; 
    assign out_select_simplify = (in_val_1 | in_val_2)[P_BUS_WIDTH-1:0]; 
    assign out_select_simplify = (in_val_1 - in_val_2)[P_BUS_WIDTH-1:0]; 
    assign out_select_simplify = (in_val_1 ^ in_val_2)[P_BUS_WIDTH-1:0]; 
    assign out_select_simplify = (in_packed_wide_data >> 8)[P_BUS_WIDTH-1:0]; 
    assign out_select_simplify = {in_val_1, in_val_2}[P_BUS_WIDTH-1:0]; 
    assign out_select_simplify = {in_val_1, in_val_2}[P_BUS_WIDTH*2-1:P_BUS_WIDTH]; 
    assign out_select_simplify = {4{in_val_1}}[P_BUS_WIDTH-1:0]; 
    assign out_select_simplify = (~in_val_1)[0 +: P_BUS_WIDTH]; 
    assign out_select_simplify = (in_val_1 & in_val_2)[0 +: P_BUS_WIDTH]; 
    assign out_select_simplify = (in_val_1 | in_val_2)[0 +: P_BUS_WIDTH]; 
    assign out_select_simplify = (in_val_1 ^ in_val_2)[0 +: P_BUS_WIDTH]; 
    assign out_reduction_simplify = &in_val_1[0];
    assign out_reduction_simplify = |in_val_1[0];
    assign out_reduction_simplify = ^in_val_1[0];
    assign out_reduction_simplify = &{in_val_1, in_val_2};
    assign out_reduction_simplify = |{in_val_1, in_val_2};
    assign out_reduction_simplify = ^{in_val_1, in_val_2};
    assign out_reduction_simplify = &(16'(in_val_1)); 
    assign out_reduction_simplify = |(16'(in_val_1));
    assign out_reduction_simplify = ^(16'(in_val_1));
    assign out_reduction_simplify = ^(P_BUS_WIDTH'hA5 ^ in_val_1);
endmodule
module AdvancedSystemVerilogFeatures (
    input logic in_clock,
    input logic in_reset,
    input logic [7:0] in_data,
    input logic [7:0] in_stream_val,
    output logic [15:0] out_multi_assign_combined,
    output logic [7:0] out_stream_packed,
    output logic [7:0] out_stream_unpacked,
    output logic out_expr_stmt_effect,
    output logic [7:0] out_enum_value,
    output logic out_jump_target_reached,
    output logic [7:0] out_class_member_access,
    output logic [7:0] out_class_method_call
);
    logic [7:0] local_array_for_assign [1:0];
    logic [7:0] local_unpacked_array [1];
    logic [15:0] local_packed_for_stream;
    enum {ITEM_START = 8'd10, ITEM_MIDDLE = 8'd20, ITEM_END = 8'd30} MyEnumT;
    class MyTestClass;
        logic [7:0] internal_member;
        function new(logic [7:0] val);
            this.internal_member = val;
        endfunction
        function automatic logic [7:0] get_member();
            return internal_member;
        endfunction
    endclass
    always_comb begin
        local_array_for_assign[0] = in_data;
        local_array_for_assign[1] = in_data + 1;
    end
    assign out_multi_assign_combined = {local_array_for_assign[1], local_array_for_assign[0]};
    assign out_stream_packed = in_stream_val;
    assign out_stream_unpacked = in_stream_val;
    typedef logic [7:0] byte_array_t [2];
    byte_array_t byte_arr_instance;
    logic [15:0] wide_packed_data;
    always_comb begin
        wide_packed_data = {in_stream_val, in_stream_val + 1};
        byte_arr_instance = {<<{wide_packed_data}};
        out_stream_packed = wide_packed_data[7:0]; 
    end
    always_comb begin
        if (in_data == 8'd5) begin end 
        out_expr_stmt_effect = (8'd10 + 8'd20); 
        if (out_multi_assign_combined != 0) begin end 
    end
    assign out_enum_value = MyEnumT.ITEM_START;
    always_ff @(posedge in_clock or negedge in_reset or (in_data == 8'd5)) begin
    end
    always_comb begin : jump_block_logic
        int temp_val;
        if (in_data > 8'd10) begin : true_branch
            temp_val = 1;
        end else begin : false_branch
            temp_val = 0;
        end
        out_jump_target_reached = (temp_val == 1);
    end
    MyTestClass my_class_instance;
    always_comb begin
        my_class_instance = new(in_data); 
        out_class_member_access = my_class_instance.internal_member; 
        out_class_method_call = my_class_instance.get_member(); 
    end
    assign out_class_member_access = (in_clock ? in_data : 8'hZZ)[0+:8];
endmodule
