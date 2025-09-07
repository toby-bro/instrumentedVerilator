module DedupeExpressions (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    input logic [7:0] in_c,
    output logic [8:0] out_sum_a,
    output logic [8:0] out_sum_b,
    output logic [8:0] out_sum_c,
    output logic out_flag1,
    output logic out_flag2,
    input logic clk_ff,
    input logic rst_ff,
    output logic [3:0] out_counter
);
    function automatic logic [8:0] calculate_sum(logic [7:0] val1, logic [7:0] val2);
        return val1 + val2 + 1;
    endfunction
    function automatic logic [8:0] calculate_sum_alt(logic [7:0] val1, logic [7:0] val2);
        return val1 + val2 + 1;
    endfunction
    function automatic logic [8:0] calculate_sum_diff(logic [7:0] val1, logic [7:0] val2);
        return val1 + val2 + 2;
    endfunction
    always_comb begin
        out_sum_a = calculate_sum(in_a, in_b); 
    end
    always_comb begin
        out_sum_b = calculate_sum_alt(in_a, in_b); 
    end
    always_comb begin
        out_sum_c = calculate_sum_diff(in_b, in_c); 
    end
    always_comb begin
        out_flag1 = (in_a > 5) && (in_b < 10) || (in_c == 7);
    end
    always_comb begin
        out_flag2 = (in_a > 5) && (in_b < 10) || (in_c == 7);
    end
    localparam int CONST_VAL_1 = 10;
    localparam int CONST_VAL_2 = CONST_VAL_1; 
    localparam int CONST_VAL_3 = 20;
    logic [3:0] counter_reg;
    always_ff @(posedge clk_ff or posedge rst_ff) begin
        if (rst_ff) begin
            counter_reg <= 4'b0;
        end else begin
            counter_reg <= counter_reg + 1;
        end
    end
    assign out_counter = counter_reg;
endmodule
module DedupeStructsClasses (
    input logic [15:0] in_data_s1,
    input logic [15:0] in_data_s2,
    input logic [7:0]  in_offset,
    output logic [15:0] out_result_s1,
    output logic [15:0] out_result_s2,
    output logic        out_class_flag,
    input logic         dummy_clk 
);
    typedef struct packed {
        logic [7:0] low;
        logic [7:0] high;
    } my_struct_t;
    class MyClass;
        rand int value;
        int id;
        function new(int init_id);
            id = init_id;
            value = 0;
        endfunction
        function int calculate_sum_class(int add_val);
            return value + add_val + id;
        endfunction
        function int get_value_common();
            return value + 10;
        endfunction
        function int get_value_common_alt();
            return value + 10;
        endfunction
    endclass
    my_struct_t struct_var1;
    my_struct_t struct_var2; 
    MyClass class_obj1;
    MyClass class_obj2; 
    my_struct_t struct_array[2];
    always_comb begin
        struct_var1.low  = in_data_s1[7:0];
        struct_var1.high = in_data_s1[15:8];
        struct_var2.low  = in_data_s2[7:0];
        struct_var2.high = in_data_s2[15:8];
        out_result_s1 = {struct_var1.high, struct_var1.low} + in_offset;
        out_result_s2 = {struct_var2.high, struct_var2.low} + in_offset; 
        struct_array[0].low = 8'hAA;
        struct_array[1].high = 8'hBB;
    end
    always_ff @(posedge dummy_clk) begin
        class_obj1 = new(1);
        class_obj2 = new(2);
        if (class_obj1.get_value_common() == class_obj2.get_value_common_alt()) begin
            out_class_flag <= 1'b1;
        end else begin
            out_class_flag <= 1'b0;
        end
    end
endmodule
module DedupeGenerate (
    input logic [7:0] gen_in,
    output logic [7:0] gen_out_sum,
    output logic [7:0] gen_out_xor,
    input logic dummy_in_gen
);
    parameter NUM_BLOCKS = 4;
    logic [7:0] block_sums [NUM_BLOCKS-1:0];
    logic [7:0] block_xors [NUM_BLOCKS-1:0];
    genvar i;
    generate
        for (i = 0; i < NUM_BLOCKS; i++) begin : gen_loop
            always_comb begin
                block_sums[i] = gen_in + i;
                block_xors[i] = gen_in ^ (i * 2);
            end
        end
    endgenerate
    generate
        for (i = 0; i < NUM_BLOCKS; i++) begin : gen_loop_alt
            localparam LP_OFFSET = 1;
            logic [7:0] temp_val;
            always_comb begin
                temp_val = gen_in + LP_OFFSET;
                if (i % 2 == 0) begin
                    block_sums[i] = temp_val;
                end else begin
                    block_sums[i] = temp_val + 1;
                end
                block_xors[i] = gen_in ^ (i * 2); 
            end
        end
    endgenerate
    always_comb begin
        gen_out_sum = 8'b0;
        gen_out_xor = 8'b0;
        for (int k = 0; k < NUM_BLOCKS; k++) begin
            gen_out_sum = gen_out_sum + block_sums[k];
            gen_out_xor = gen_out_xor ^ block_xors[k];
        end
        if (dummy_in_gen) begin
            gen_out_sum = gen_out_sum + 1;
        end
    end
endmodule
module DedupeAdvancedTypes (
    input logic [1:0] selector_in,
    input logic [7:0] data_in_md1,
    input logic [7:0] data_in_md2,
    output logic [7:0] data_out_md,
    output logic [7:0] out_enum_val,
    output logic [7:0] out_union_val
);
    typedef enum {
        STATE_IDLE,
        STATE_ACTIVE,
        STATE_DONE,
        STATE_ERROR
    } state_e;
    typedef enum {
        MODE_IDLE,
        MODE_ACTIVE,
        MODE_DONE,
        MODE_ERROR
    } mode_e;
    state_e current_state;
    mode_e current_mode;
    typedef union packed {
        logic [7:0] byte_val;
        logic [3:0] nibble_a;
        logic [3:0] nibble_b;
    } my_union_t;
    my_union_t union_var1;
    my_union_t union_var2; 
    logic [7:0] matrix1 [2][2];
    logic [7:0] matrix2 [2][2]; 
    typedef logic [7:0] data_array_t [4];
    data_array_t array_inst1;
    data_array_t array_inst2; 
    always_comb begin
        case (selector_in)
            2'b00: current_state = STATE_IDLE;
            2'b01: current_state = STATE_ACTIVE;
            2'b10: current_state = STATE_DONE;
            default: current_state = STATE_ERROR;
        endcase
        case (selector_in)
            2'b00: current_mode = MODE_IDLE;
            2'b01: current_mode = MODE_ACTIVE;
            2'b10: current_mode = MODE_DONE;
            default: current_mode = MODE_ERROR;
        endcase
        out_enum_val = (current_state == STATE_ACTIVE) ? 8'hAA : 8'hBB;
        union_var1.byte_val = data_in_md1;
        union_var2.byte_val = data_in_md2;
        out_union_val = union_var1.byte_val + union_var2.byte_val;
        matrix1[0][0] = data_in_md1;
        matrix1[0][1] = data_in_md1 + 1;
        matrix1[1][0] = data_in_md1 + 2;
        matrix1[1][1] = data_in_md1 + 3;
        matrix2[0][0] = data_in_md1;
        matrix2[0][1] = data_in_md1 + 1;
        matrix2[1][0] = data_in_md1 + 2;
        matrix2[1][1] = data_in_md1 + 3;
        if (selector_in[0]) begin
            data_out_md = matrix1[1][1];
        end else begin
            data_out_md = matrix2[0][0];
        end
        array_inst1[0] = 8'h11;
        array_inst1[1] = 8'h22;
        array_inst2[0] = 8'h11; 
        array_inst2[1] = 8'h22; 
    end
endmodule
module DedupeControlFlow (
    input logic [3:0] sel_val1,
    input logic [3:0] sel_val2,
    input logic [7:0] val_a,
    input logic [7:0] val_b,
    output logic [7:0] out_ctrl_1,
    output logic [7:0] out_ctrl_2,
    output logic [7:0] out_case_1,
    output logic [7:0] out_case_2
);
    const logic [7:0] C_CONST_1 = 8'hF0;
    const logic [7:0] C_CONST_2 = 8'hF0; 
    const logic [7:0] C_CONST_3 = 8'h0F;
    always_comb begin
        if (sel_val1 > 5 && sel_val2 < 10) begin
            out_ctrl_1 = val_a + C_CONST_1;
        end else if (sel_val1 == 0 || sel_val2 == 0) begin
            out_ctrl_1 = val_b - C_CONST_1;
        end else begin
            out_ctrl_1 = 8'hFF;
        end
    end
    always_comb begin
        if (sel_val1 > 5 && sel_val2 < 10) begin
            out_ctrl_2 = val_a + C_CONST_2; 
        end else if (sel_val1 == 0 || sel_val2 == 0) begin
            out_ctrl_2 = val_b - C_CONST_2;
        end else begin
            out_ctrl_2 = 8'hFF;
        end
    end
    always_comb begin
        case (sel_val1)
            4'd0: out_case_1 = val_a;
            4'd1: out_case_1 = val_b;
            4'd2: out_case_1 = val_a + val_b;
            default: out_case_1 = C_CONST_3;
        endcase
    end
    always_comb begin
        case (sel_val1)
            4'd0: out_case_2 = val_a;
            4'd1: out_case_2 = val_b;
            4'd2: out_case_2 = val_a + val_b;
            default: out_case_2 = C_CONST_3;
        endcase
    end
    always_comb begin
        unique if (sel_val1 == 1) begin
            out_ctrl_1 = val_a + val_b;
        end else if (sel_val1 == 2) begin
            out_ctrl_1 = val_a - val_b;
        end else begin
            out_ctrl_1 = val_a ^ val_b;
        end
        priority case (sel_val2)
            4'd0: out_case_1 = val_a;
            4'd1: out_case_1 = val_b;
            default: out_case_1 = 8'h00;
        endcase
    end
endmodule
module DedupeTasks (
    input logic [7:0] task_in_a,
    input logic [7:0] task_in_b,
    input logic [7:0] task_in_c,
    output logic [7:0] task_out_res1,
    output logic [7:0] task_out_res2,
    output logic [7:0] task_out_ref_sum
);
    task automatic calculate_product (
        input logic [7:0] op1,
        input logic [7:0] op2,
        output logic [7:0] result
    );
        result = op1 * op2;
    endtask
    task automatic calculate_product_alt (
        input logic [7:0] op1,
        input logic [7:0] op2,
        output logic [7:0] result
    );
        result = op1 * op2;
    endtask
    task automatic add_with_ref (
        input logic [7:0] val1,
        input logic [7:0] val2,
        ref logic [7:0] sum_out
    );
        sum_out = val1 + val2;
    endtask
    task automatic add_with_ref_alt (
        input logic [7:0] val1,
        input logic [7:0] val2,
        ref logic [7:0] sum_out
    );
        sum_out = val1 + val2;
    endtask
    logic [7:0] temp_sum;
    always_comb begin
        calculate_product(task_in_a, task_in_b, task_out_res1);
        calculate_product_alt(task_in_a, task_in_c, task_out_res2); 
        add_with_ref(task_in_a, task_in_b, temp_sum);
        task_out_ref_sum = temp_sum;
        add_with_ref_alt(task_in_c, task_in_b, task_out_ref_sum);
    end
endmodule
