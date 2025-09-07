module BasicTypesModule (
    input logic [7:0] in_data_m1,
    output logic [15:0] out_result_m1
);
    logic a_s1;
    logic [1:0] b_s1;
    logic [7:0] c_s2;
    logic [15:0] d_s3;
    logic [31:0] e_s5;
    logic [63:0] f_s6;
    int i_val_s5;
    longint l_val_s6;
    byte b_val_s2;
    bit u_bit_s1;
    logic [127:0] large_packed_vec_s10;
    always_comb begin
        a_s1 = in_data_m1[0];
        b_s1 = in_data_m1[1:0];
        c_s2 = in_data_m1;
        d_s3 = {in_data_m1, in_data_m1};
        e_s5 = {d_s3, d_s3};
        f_s6 = {e_s5, e_s5[31:0]};
        i_val_s5 = int'(in_data_m1) + 10;
        l_val_s6 = longint'(in_data_m1) * 20;
        b_val_s2 = in_data_m1[7:0];
        u_bit_s1 = in_data_m1[2];
        large_packed_vec_s10 = {128{u_bit_s1}} + l_val_s6;
        out_result_m1 = d_s3 + {c_s2, a_s1};
    end
endmodule
module ComplexDataTypesModule (
    input bit [3:0] s_in_m2,
    output int s_out_m2
);
    typedef enum {STATE_IDLE, STATE_ACTIVE, STATE_DONE} StateType_t;
    StateType_t current_state_m2;
    typedef struct packed {
        logic [7:0] field1;
        int field2;
    } MyPackedStruct_t;
    MyPackedStruct_t my_packed_struct_m2;
    struct {
        logic anon_field1;
        logic [15:0] anon_field2;
    } anon_struct_var_m2;
    union {
        int i_union_m2;
        real r_union_m2;
    } my_union_var_m2;
    MyPackedStruct_t struct_array_m2[2];
    struct {
        logic [3:0] s_a;
        bit s_b;
    } anon_struct_array_m2[3];
    always_comb begin
        current_state_m2 = (s_in_m2 == 4'b0001) ? STATE_ACTIVE : STATE_IDLE;
        if (s_in_m2 == 4'b0010) current_state_m2 = STATE_DONE;
        my_packed_struct_m2.field1 = s_in_m2[3:0] + 8'hAA;
        my_packed_struct_m2.field2 = int'(s_in_m2) * 5;
        anon_struct_var_m2.anon_field1 = s_in_m2[0];
        anon_struct_var_m2.anon_field2 = {12'h0, s_in_m2[3:0]};
        my_union_var_m2.i_union_m2 = int'(s_in_m2) + 100;
        struct_array_m2[0].field1 = s_in_m2 + 8'h01;
        struct_array_m2[1].field2 = int'(s_in_m2) + 200;
        anon_struct_array_m2[0].s_a = s_in_m2;
        anon_struct_array_m2[1].s_b = s_in_m2[1];
        s_out_m2 = my_packed_struct_m2.field2 + my_union_var_m2.i_union_m2 + struct_array_m2[1].field2;
    end
endmodule
module ProceduralLogicModule (
    input logic clk_m3,
    input logic reset_n_m3,
    input int data_in_m3,
    output int data_out_m3
);
    int reg_data_m3;
    logic [3:0] counter_m3;
    class MySimpleClass;
        rand int class_member_val;
        function new(int init_val);
            class_member_val = init_val;
        endfunction
        function int get_val();
            return class_member_val;
        endfunction
    endclass
    MySimpleClass my_object_handle;
    function automatic int add_func(input int val);
        static int static_func_call_count = 0;
        int local_func_var;
        local_func_var = val + static_func_call_count;
        static_func_call_count = static_func_call_count + 1;
        return local_func_var;
    endfunction
    task automatic process_task(input int val_in, output int val_out);
        static byte static_task_counter = 0;
        logic [7:0] local_task_arr[4];
        int i_task;
        val_out = val_in + static_task_counter;
        for (i_task = 0; i_task < 4; i_task++) begin
            local_task_arr[i_task] = val_in[7:0] + i_task;
        end
        static_task_counter = static_task_counter + 1;
    endtask
    always_ff @(posedge clk_m3 or negedge reset_n_m3) begin
        if (!reset_n_m3) begin
            reg_data_m3 <= 0;
            counter_m3 <= 0;
            data_out_m3 <= 0;
            if (my_object_handle != null) begin
                my_object_handle.class_member_val = 0;
            end
        end else begin
            reg_data_m3 <= add_func(data_in_m3);
            counter_m3 <= counter_m3 + 1;
            process_task(reg_data_m3, data_out_m3);
            if (my_object_handle != null) begin
                my_object_handle.class_member_val = data_in_m3;
            end
        end
    end
    logic temp_comb_var;
    always_comb begin
        temp_comb_var = counter_m3[0];
        if (my_object_handle == null) begin
            my_object_handle = new(data_in_m3);
        end
        temp_comb_var = temp_comb_var ^ my_object_handle.get_val()[0];
    end
endmodule
module LargeArraysAndRealModule (
    input real r_in_m4,
    output real r_out_m4
);
    real pi_val_m4 = 3.14159;
    shortreal e_val_m4 = 2.718;
    time current_time_m4;
    realtime elapsed_time_m4;
    logic [7:0] large_2d_array_m4 [10][10];
    int int_array_m4 [5];
    parameter int ARRAY_DIM = 5;
    localparam string MODULE_IDENTIFIER = "LAM_v1";
    always_comb begin
        r_out_m4 = r_in_m4 * pi_val_m4 + e_val_m4;
        current_time_m4 = $time;
        elapsed_time_m4 = $realtime;
        for (int i=0; i < ARRAY_DIM; i++) begin
            int_array_m4[i] = int'(r_in_m4 * i);
            for (int j=0; j < 10; j++) begin
                large_2d_array_m4[i][j] = int_array_m4[i][7:0] + j;
            end
        end
        r_out_m4 = r_out_m4 + int_array_m4[0] + large_2d_array_m4[0][0];
    end
endmodule
module MixedPortsAndLogicModule (
    input bit enable_m5,
    input logic [7:0] port_data_m5,
    output logic [15:0] port_output_m5,
    output logic clk_out_m5,
    inout logic [31:0] bidirectional_signal_m5
);
    logic internal_clock_m5;
    logic [7:0] reg_a_m5, reg_b_m5;
    int counter_val_m5;
    logic [1:0] small_vec_m5;
    logic [31:0] bidirectional_driver_m5;
    logic bidirectional_enable_m5;
    localparam int MAX_COUNT_M5 = 100;
    parameter string MODULE_NAME_M5 = "MixedModule";
    function automatic int calc_sum(input int val1, input int val2);
        return val1 + val2 + MAX_COUNT_M5;
    endfunction
    always_comb begin
        internal_clock_m5 = enable_m5;
        clk_out_m5 = internal_clock_m5;
        port_output_m5 = {reg_b_m5, reg_a_m5} + calc_sum(counter_val_m5, 10);
        if (port_data_m5[0]) begin
            bidirectional_driver_m5 = counter_val_m5;
            bidirectional_enable_m5 = 1'b1;
            small_vec_m5 = 2'b0;
        end else begin
            bidirectional_driver_m5 = '0;
            bidirectional_enable_m5 = 1'b0;
            small_vec_m5 = bidirectional_signal_m5[1:0];
        end
    end
    assign bidirectional_signal_m5 = bidirectional_enable_m5 ? bidirectional_driver_m5 : 'z;
    always_ff @(posedge internal_clock_m5) begin
        if (enable_m5) begin
            reg_a_m5 <= port_data_m5;
            reg_b_m5 <= reg_a_m5 + 1;
            counter_val_m5 <= counter_val_m5 + 1;
        end
    end
endmodule
