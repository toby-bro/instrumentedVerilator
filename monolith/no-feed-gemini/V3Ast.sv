module Module_BasicOpsAndTypes (
    input logic [15:0] in_data_a,
    input logic [7:0] in_data_b,
    input int in_int_c,
    input byte in_byte_d,
    input signed int in_sint_e,
    output logic [15:0] out_result_sum,
    output int out_result_cast,
    output signed longint out_signed_result,
    output logic [31:0] out_width_change,
    output bit [2:0] out_bit_result
);
    logic [15:0] local_reg_a;
    logic [7:0] local_reg_b;
    int local_int_c;
    byte local_byte_d;
    signed int local_sint_e;
    signed logic [15:0] signed_logic_var;
    unsigned logic [15:0] unsigned_logic_var;
    always_comb begin
        local_reg_a = in_data_a;
        local_reg_b = in_data_b;
        local_int_c = in_int_c;
        local_byte_d = in_byte_d;
        local_sint_e = in_sint_e;
        out_result_sum = local_reg_a + {8'd0, local_reg_b}; 
        out_result_cast = int'(local_reg_a); 
        signed_logic_var = 16'shABCD; 
        unsigned_logic_var = 16'h1234; 
        out_signed_result = $signed(unsigned_logic_var) + signed_logic_var; 
        out_width_change = 32'(local_int_c * local_sint_e); 
        out_bit_result = 3'b101;
        out_bit_result[1] = local_reg_b[0]; 
    end
    localparam P_INT = 100;
    localparam P_LONGINT = 64'd123456789012345;
    localparam P_BYTE = 8'd255;
    localparam signed P_SIGNED_INT = -50;
    logic [7:0] constant_calc_result;
    always_comb begin
        constant_calc_result = P_BYTE + P_INT; 
    end
endmodule
module Module_ComplexStatementsAndLists (
    input logic [7:0] control_in,
    input logic [3:0] sel_in,
    input logic [1:0] loop_limit,
    output logic [7:0] out_val_a,
    output logic [7:0] out_val_b,
    output logic [7:0] out_val_c
);
    logic [7:0] temp_a, temp_b, temp_c;
    logic [7:0] loop_sum;
    always_comb begin : main_block
        temp_a = 8'd0;
        temp_b = 8'd0;
        temp_c = 8'd0;
        loop_sum = 8'd0;
        if (control_in[0]) begin : if_block_0
            temp_a = control_in + 1;
            temp_b = control_in - 1;
        end else if (control_in[1]) begin : if_block_1
            temp_a = control_in * 2;
        end else begin : if_block_2
            temp_b = control_in / 2;
            temp_c = control_in % 2;
        end
        case (sel_in)
            4'd0: temp_c = temp_a | temp_b;
            4'd1: begin : case_1_block
                temp_c = temp_a & temp_b;
                temp_a = temp_c + 5;
            end
            4'd2: temp_c = temp_a ^ temp_b;
            default: begin : case_default_block
                temp_a = 8'dFF;
                temp_b = 8'd00;
                temp_c = 8'dAA;
            end
        endcase
        for (int i = 0; i < loop_limit; i++) begin : for_block
            loop_sum = loop_sum + i;
            if (i == 1) loop_sum = loop_sum + 10;
        end
        out_val_a = temp_a;
        out_val_b = temp_b + loop_sum;
        out_val_c = temp_c;
    end
endmodule
module Module_StructuresAndClasses (
    input logic [7:0] data_in,
    input byte sel_byte,
    input shortint temp_short_in,
    input int class_ptr_val, 
    output logic [15:0] result_out,
    output bit is_odd
);
    typedef enum { RED, GREEN, BLUE, YELLOW } color_t;
    color_t my_color;
    typedef struct packed {
        logic [7:0] field1;
        logic [3:0] field2;
        logic       flag;
    } my_struct_t;
    my_struct_t s_var;
    typedef union packed {
        logic [15:0] word;
        struct packed {
            logic [7:0] byte1;
            logic [7:0] byte0;
        } bytes;
    } my_union_t;
    my_union_t u_var;
    class BaseClass;
        int value;
        function new(int v); value = v; endfunction
        virtual function int get_value(); return value; endfunction
    endclass
    class DerivedClass extends BaseClass;
        int multiplier;
        function new(int v, int m); super.new(v); multiplier = m; endfunction
        virtual function int get_value(); return value * multiplier; endfunction
    endclass
    BaseClass base_obj_handle;
    DerivedClass derived_obj_handle;
    BaseClass generic_obj_handle;
    always_comb begin
        my_color = GREEN;
        if (data_in > 100) my_color = RED;
        result_out[7:0] = my_color; 
        s_var.field1 = data_in;
        s_var.field2 = sel_byte[3:0];
        s_var.flag = data_in[0];
        result_out[15:8] = s_var.field1 + {4'b0, s_var.field2}; 
        u_var.word = {sel_byte, data_in};
        result_out = result_out + u_var.bytes.byte0 + u_var.bytes.byte1;
        is_odd = s_var.flag;
        if (class_ptr_val == 0) begin
            base_obj_handle = new(10);
            derived_obj_handle = new(20, 2);
        end else if (class_ptr_val == 1) begin
            generic_obj_handle = base_obj_handle;
        end else begin
            generic_obj_handle = derived_obj_handle; 
        end
    end
    function void dummy_task(input int val);
        int temp = val * 2;
    endfunction
endmodule
module Module_NameEncodingAndHierarchy (
    input logic [7:0] data_in,
    input logic [7:0] data_out_val,
    output logic [7:0] out_data_hierarchical
);
    localparam MY_CONSTANT = 8'hAA;
    logic __PVT__private_signal;
    logic __DOT__dotted_signal;
    logic __BRA__bracketed_signal__KET__; 
    logic __02Dnegative_value; 
    SubModule Instance__DOT__SubInstance (
        .sub_in(data_in),
        .sub_out(out_data_hierarchical)
    );
    always_comb begin
        __PVT__private_signal = data_in + MY_CONSTANT;
        __DOT__dotted_signal = __PVT__private_signal;
        __BRA__bracketed_signal__KET__ = __DOT__dotted_signal;
        __02Dnegative_value = data_out_val; 
        out_data_hierarchical = __BRA__bracketed_signal__KET__;
    end
endmodule
module SubModule (
    input logic [7:0] sub_in,
    output logic [7:0] sub_out
);
    logic [7:0] internal_reg;
    always_comb begin
        internal_reg = sub_in * 2;
        sub_out = internal_reg;
    end
endmodule
module Module_AdvancedExpressions (
    input logic [7:0] in_op1,
    input logic [7:0] in_op2,
    input logic [2:0] sel_val,
    output logic [15:0] result_concat,
    output logic [7:0] result_function_call,
    output logic [7:0] result_replicate
);
    function automatic logic [7:0] calculate_complex(input logic [7:0] a, input logic [7:0] b, input logic [2:0] s);
        logic [7:0] temp;
        if (s == 3'd0) begin
            temp = a + b;
        end else if (s == 3'd1) begin
            temp = a - b;
        end else if (s == 3'd2) begin
            temp = a * b;
        end else begin
            temp = a / (b + 1); 
        end
        return temp;
    endfunction
    function automatic logic [7:0] another_func(input logic [7:0] val);
        return val ^ 8'hF0;
    endfunction
    always_comb begin
        result_concat = {in_op1, in_op2};
        result_replicate = {8{in_op1[0]}}; 
        result_function_call = another_func(calculate_complex(in_op1, in_op2, sel_val));
        logic [7:0] temp_ternary;
        temp_ternary = (in_op1 > in_op2) ? in_op1 : in_op2;
        result_function_call = result_function_call + temp_ternary;
    end
endmodule
module Module_QueueAndVoid (
    input logic [7:0] data_in,
    input int q_pop_val,
    output logic [7:0] q_out_val
);
    logic [7:0] my_queue [$]; 
    always_comb begin
        my_queue.push_back(data_in);
        my_queue.push_front(data_in + 1);
        my_queue.insert(0, data_in + 2);
        if (!my_queue.empty()) begin
            q_out_val = my_queue[0]; 
            if (q_pop_val > 0) begin
                q_out_val = my_queue.pop_front(); 
            end
        end else begin
            q_out_val = 8'hXX; 
        end
        my_queue.delete(); 
    end
    task void process_queue_task(input logic [7:0] val);
        logic [7:0] temp_val = val * 3;
    endtask
endmodule
