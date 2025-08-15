module module_basic_vars (
    input  logic [7:0] in_data_8bit,
    input  logic [15:0] in_data_16bit,
    input  logic [31:0] in_data_32bit,
    input  logic [63:0] in_data_64bit,
    output logic [7:0] out_data_8bit,
    output logic [15:0] out_data_16bit,
    output logic [31:0] out_data_32bit,
    output logic [63:0] out_data_64bit
);
    logic [7:0]   local_reg_8bit;
    logic [15:0]  local_reg_16bit;
    logic [31:0]  local_reg_32bit;
    logic [63:0]  local_reg_64bit;
    logic         single_bit_var;
    logic [3:0]   four_bit_var;
    logic [7:0]   unpacked_array_1 [0:3];
    logic         unpacked_array_2 [0:7];
    always_comb begin
        local_reg_8bit   = in_data_8bit + 1;
        local_reg_16bit  = in_data_16bit + local_reg_8bit;
        local_reg_32bit  = in_data_32bit + local_reg_16bit;
        local_reg_64bit  = in_data_64bit + local_reg_32bit;
        single_bit_var   = (local_reg_8bit[0] ^ local_reg_16bit[0]);
        four_bit_var     = local_reg_8bit[3:0] + unpacked_array_2[0];
        unpacked_array_1[0] = in_data_8bit;
        unpacked_array_1[1] = in_data_8bit + 2;
        unpacked_array_1[2] = in_data_8bit + 3;
        unpacked_array_1[3] = in_data_8bit + 4;
        unpacked_array_2[0] = single_bit_var;
        unpacked_array_2[1] = ~single_bit_var;
        out_data_8bit   = local_reg_8bit;
        out_data_16bit  = local_reg_16bit;
        out_data_32bit  = local_reg_32bit;
        out_data_64bit  = local_reg_64bit;
    end
endmodule
module module_advanced_types (
    input  logic clk,
    input  logic reset_n,
    input  logic in_enable,
    output logic [3:0] out_state
);
    chandle opaque_handle;
    event   trigger_event;
    static integer static_counter;
    typedef enum bit [1:0] { IDLE, START, BUSY, DONE } fsm_state_e;
    fsm_state_e current_state;
    fsm_state_e next_state;
    struct {
        logic [7:0]  anon_field1;
        logic [15:0] anon_field2;
    } anonymous_struct_var;
    typedef struct packed {
        logic [2:0] foo;
        logic       bar;
    } my_struct_t;
    my_struct_t named_struct_var;
    class MyClass;
        int value;
        function new(int init_val);
            this.value = init_val;
        endfunction
        function int get_value();
            return value;
        endfunction
    endclass
    MyClass my_object_handle;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            current_state                     <= IDLE;
            static_counter                    <= 0;
            my_object_handle                  <= null;
            anonymous_struct_var.anon_field1  <= 8'h0;
            anonymous_struct_var.anon_field2  <= 16'h0;
            named_struct_var.foo              <= 3'b0;
            named_struct_var.bar              <= 1'b0;
        end else begin
            if (my_object_handle == null) begin
                my_object_handle <= new MyClass(100);
            end
            current_state <= next_state;
            if (in_enable) begin
                static_counter <= static_counter + 1;
                if (static_counter > 5) -> trigger_event;
            end
            anonymous_struct_var.anon_field1 <= static_counter[7:0];
            named_struct_var.foo             <= current_state;
        end
    end
    always_comb begin
        next_state = current_state;
        case (current_state)
            IDLE:  if (in_enable) next_state = START;
            START: next_state = BUSY;
            BUSY:  if (static_counter > 10) next_state = DONE;
            DONE:  next_state = IDLE;
        endcase
        out_state = current_state;
    end
endmodule
module module_functions_tasks (
    input  logic clk,
    input  logic [7:0] in_val,
    output logic [7:0] out_result
);
    logic [7:0] internal_data_a_comb;
    logic [7:0] internal_data_b;
    logic [7:0] temp_val;
    logic [7:0] sequential_reg_data;
    function automatic logic [7:0] calculate_sum(logic [7:0] a, logic [7:0] b);
        logic [7:0] func_local_var;
        func_local_var = a + b;
        return func_local_var;
    endfunction
    task automatic process_data(input logic [7:0] data_in, output logic [7:0] data_out);
        logic [7:0] task_local_var;
        task_local_var = data_in * 2;
        data_out = task_local_var;
    endtask
    always_comb begin
        internal_data_a_comb = calculate_sum(in_val, 8'd5);
        process_data(internal_data_a_comb, internal_data_b);
        temp_val = internal_data_a_comb + internal_data_b + sequential_reg_data;
        out_result = temp_val;
    end
    always_ff @(posedge clk) begin
        if (internal_data_a_comb[0]) begin
            sequential_reg_data <= sequential_reg_data + 1;
        end else begin
            sequential_reg_data <= 8'b0;
        end
    end
endmodule
module module_mixed_logic (
    input  logic        i_clk,
    input  logic        i_rst_n,
    input  logic [3:0]  i_control,
    input  logic [63:0] i_data_in,
    output logic [63:0] o_data_out,
    output logic        o_status_bit
);
    logic [63:0]  reg_pipeline [0:2];
    logic [31:0]  counter;
    logic         flag_a;
    logic         flag_b;
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            reg_pipeline[0] <= 64'd0;
            reg_pipeline[1] <= 64'd0;
            reg_pipeline[2] <= 64'd0;
            counter         <= 32'd0;
            flag_a          <= 1'b0;
            flag_b          <= 1'b0;
        end else begin
            reg_pipeline[0] <= i_data_in;
            reg_pipeline[1] <= reg_pipeline[0] + counter;
            reg_pipeline[2] <= reg_pipeline[1] * 2;
            if (i_control[0]) begin
                counter <= counter + 1;
            end else begin
                counter <= 32'd0;
            end
            flag_a <= (counter > 100);
            flag_b <= (i_control[1] && flag_a);
        end
    end
    always_comb begin
        o_data_out = reg_pipeline[2];
        o_status_bit = flag_a && flag_b;
    end
endmodule
module module_complex_arrays (
    input  logic [7:0] data_val_in,
    output logic [7:0] array_sum_out
);
    logic [31:0] large_unpacked_array [0:15];
    typedef struct packed {
        logic [7:0] id;
        logic [7:0] value;
        bit         valid;
    } entry_t;
    entry_t struct_array [0:7];
    logic [7:0] temp_sum;
    always_comb begin
        temp_sum = 8'b0;
        for (int i = 0; i <= 15; i++) begin
            large_unpacked_array[i] = data_val_in + i;
        end
        for (int i = 0; i <= 7; i++) begin
            struct_array[i].id = i;
            struct_array[i].value = data_val_in + i;
            struct_array[i].valid = (i % 2 == 0);
        end
        for (int i = 0; i <= 7; i++) begin
            if (struct_array[i].valid) begin
                temp_sum = temp_sum + struct_array[i].value;
            end
        end
        array_sum_out = temp_sum;
    end
endmodule
