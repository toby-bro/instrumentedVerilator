class MyClassForProceduralInstantiation;
    logic [15:0] data_member;
    function new(logic [15:0] init_data);
        data_member = init_data;
    endfunction
    function logic [15:0] get_data();
        return data_member;
    endfunction
    function void set_data(logic [15:0] new_data);
        data_member = new_data;
    endfunction
endclass
module basic_ops_and_constants (
    input  logic [7:0] in_data,
    input  logic       in_sel,
    output logic [7:0] out_result_packed,
    output logic [1:0] out_part_select,
    output logic [7:0] out_cond_val,
    output logic       out_single_bit,
    output int         out_const_add_result
);
    localparam int CONST_A = 10;
    localparam int CONST_B = 20;
    localparam bit [7:0] MASK_VAL = 8'hF0;
    localparam int CONST_C = 10;
    localparam int LITERAL_CONST_D = 30;
    logic [7:0] intermediate_op_a;
    logic [7:0] intermediate_op_b;
    logic [7:0] intermediate_op_c;
    assign out_single_bit = in_data[0];
    assign out_part_select = in_data[3:2];
    logic [1:0] identical_part_select_val;
    assign identical_part_select_val = in_data[3:2];
    assign out_cond_val = in_sel ? intermediate_op_a : intermediate_op_b;
    assign intermediate_op_a = in_data + CONST_A;
    assign intermediate_op_b = in_data - CONST_B;
    assign intermediate_op_c = intermediate_op_a * intermediate_op_b;
    assign out_result_packed = (intermediate_op_c & MASK_VAL) | out_part_select;
    logic [7:0] common_expr_res1;
    logic [7:0] common_expr_res2;
    assign common_expr_res1 = in_data + (CONST_A * 2);
    assign common_expr_res2 = in_data + (CONST_A * 2);
    assign out_const_add_result = CONST_A + CONST_C;
    logic [7:0] var_for_comparison_1;
    logic [7:0] var_for_comparison_2;
    assign var_for_comparison_1 = in_data + 1;
    assign var_for_comparison_2 = in_data + 2;
endmodule
module unpacked_array_ops (
    input  logic [7:0] in_elem_val,
    input  int         in_idx,
    output logic [7:0] out_indexed_val,
    output logic [7:0] out_array_elem_sum
);
    logic [7:0] my_unpacked_array [0:3];
    logic [7:0] other_unpacked_array [0:3];
    assign my_unpacked_array = '{in_elem_val,
                                 in_elem_val + 1,
                                 in_elem_val + 2,
                                 in_elem_val + 3};
    assign other_unpacked_array = '{in_elem_val,
                                    in_elem_val + 1,
                                    in_elem_val + 2,
                                    in_elem_val + 3};
    assign out_indexed_val = my_unpacked_array[in_idx % 4];
    assign out_array_elem_sum = my_unpacked_array[0] + other_unpacked_array[1];
endmodule
module packed_struct_ops (
    input  logic       in_bit_p,
    input  logic [3:0] in_nibble_q,
    input  logic [7:0] in_byte_r,
    input  logic [15:0] in_halfword_s,
    output logic [31:0] out_combined_val_p,
    output logic [7:0] out_extracted_byte_p,
    inout  logic [3:0] io_status_reg_p
);
    typedef struct packed {
        logic       field_a;
        logic [3:0] field_b;
        logic [7:0] field_c;
    } my_packed_struct_type_p;
    my_packed_struct_type_p instance_struct_p;
    logic [31:0] temp_combined_packed;
    logic [3:0] internal_status;
    logic [7:0] rep_bit_p_8;
    logic [7:0] rep_nibble_q0_8;
    logic [15:0] rep_a; 
    logic [15:0] rep_b; 
    assign instance_struct_p = '{field_a: in_bit_p, field_b: in_nibble_q, field_c: in_byte_r};
    assign temp_combined_packed = { instance_struct_p.field_a, instance_struct_p.field_b, instance_struct_p.field_c,
                                    in_halfword_s, {2{in_bit_p}} };
    assign out_combined_val_p = temp_combined_packed;
    assign out_extracted_byte_p = instance_struct_p.field_c;
    assign io_status_reg_p = internal_status;
    assign internal_status = in_nibble_q + 1;
    assign rep_bit_p_8 = {8{in_bit_p}};
    assign rep_nibble_q0_8 = {8{in_nibble_q[0]}};
    assign rep_a = {rep_bit_p_8, rep_nibble_q0_8};
    assign rep_b = {rep_bit_p_8, rep_nibble_q0_8};
endmodule
module procedural_logic_and_class (
    input  logic [15:0] val_in_x,
    input  logic [15:0] val_in_y,
    input  logic        control_flag,
    output logic [15:0] val_out_proc_block,
    output logic [15:0] val_out_from_class,
    output logic [15:0] val_out_alias_final
);
    logic [15:0] temp_val_proc_1;
    logic [15:0] temp_val_proc_2;
    logic [15:0] aliased_signal;
    MyClassForProceduralInstantiation my_class_obj;
    always_comb begin
        logic [15:0] complex_subexpr_a;
        logic [15:0] complex_subexpr_b;
        if (control_flag) begin
            temp_val_proc_1 = val_in_x + val_in_y;
        end else begin
            temp_val_proc_1 = val_in_x - val_in_y;
        end
        my_class_obj = new(temp_val_proc_1);
        my_class_obj.set_data(temp_val_proc_1 + 10);
        val_out_from_class = my_class_obj.get_data();
        aliased_signal = temp_val_proc_1;
        temp_val_proc_2 = aliased_signal + 1;
        aliased_signal = val_in_y;
        val_out_proc_block = temp_val_proc_2;
        val_out_alias_final = aliased_signal;
        complex_subexpr_a = (val_in_x | val_in_y) & (val_in_x ^ val_in_y);
        complex_subexpr_b = (val_in_x | val_in_y) & (val_in_x ^ val_in_y);
        val_out_proc_block = val_out_proc_block + complex_subexpr_a[0];
        val_out_from_class = val_out_from_class + complex_subexpr_b[1];
    end
endmodule
module enum_struct_array_ops (
    input  logic [7:0] in_input_val1,
    input  logic [7:0] in_input_val2,
    input  logic       in_enum_select,
    output logic [15:0] out_calculated_sum,
    output logic [7:0] out_array_struct_data
);
    typedef enum logic [1:0] {
        STATE_READY = 2'b00,
        STATE_BUSY = 2'b01,
        STATE_FINISH = 2'b10
    } sys_state_e;
    sys_state_e current_sys_state;
    typedef struct packed {
        sys_state_e state;
        logic [7:0] data;
    } packet_info_t;
    packet_info_t packet_buffer_inst [0:1];
    logic [7:0] temp_intermediate_val;
    always_comb begin
        if (in_enum_select) begin
            current_sys_state = STATE_BUSY;
            temp_intermediate_val = in_input_val1;
        end else begin
            current_sys_state = STATE_READY;
            temp_intermediate_val = in_input_val2;
        end
        packet_buffer_inst[0].state = current_sys_state;
        packet_buffer_inst[0].data = temp_intermediate_val + 5;
        packet_buffer_inst[1].state = STATE_FINISH;
        packet_buffer_inst[1].data = in_input_val1 + in_input_val2;
        out_calculated_sum = {packet_buffer_inst[0].state, packet_buffer_inst[0].data} + packet_buffer_inst[1].data;
        out_array_struct_data = packet_buffer_inst[1].data;
    end
endmodule
module clocked_logic (
    input  logic clk_i,
    input  logic rst_ni,
    input  logic en_i,
    input  logic [7:0] data_sync_in,
    input  logic [7:0] data_latch_in,
    output logic [7:0] reg_out_q,
    output logic [7:0] latch_out_q,
    output logic [7:0] comb_out_from_reg
);
    logic [7:0] sync_reg_internal;
    logic [7:0] latch_reg_internal;
    logic [7:0] temp_local_var;
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            sync_reg_internal <= 8'h00;
        end else if (en_i) begin
            sync_reg_internal <= data_sync_in + 1;
        end else begin
            sync_reg_internal <= data_sync_in;
        end
    end
    always_latch begin
        if (en_i) begin
            latch_reg_internal = data_latch_in;
        end
    end
    assign reg_out_q = sync_reg_internal;
    assign latch_out_q = latch_reg_internal;
    assign comb_out_from_reg = sync_reg_internal + latch_reg_internal;
    logic [7:0] local_val_1;
    logic [7:0] local_val_2;
    assign local_val_1 = data_sync_in + 10;
    assign temp_local_var = local_val_1;
    assign local_val_2 = temp_local_var + 1;
endmodule
