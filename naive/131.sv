module BasicCombinational (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    output logic [7:0] out_add,
    output logic [7:0] out_sub,
    output logic [7:0] out_mul
);
    parameter WIDTH = 8;
    localparam MAX_VAL = (1 << WIDTH) - 1;
    assign out_add = in_a + in_b;
    always_comb begin
        if (in_a >= in_b) begin
            out_sub = in_a - in_b;
        end else begin
            out_sub = in_b - in_a;
        end
    end
    always_comb begin
        case (in_a[1:0])
            2'b00: out_mul = in_a * 1;
            2'b01: out_mul = in_a * 2;
            2'b10: out_mul = in_a * 3;
            default: out_mul = in_a * 4;
        endcase
    end
endmodule
module SequentialAndArrays (
    input logic clk,
    input logic rst_n,
    input logic [3:0] data_in,
    output logic [3:0] data_out_reg,
    output logic [7:0] array_sum_out
);
    logic [3:0] register_q;
    logic [3:0] my_packed_array [0:3];
    logic [7:0] my_unpacked_array [0:2][0:3];
    function automatic logic [7:0] calculate_sum (logic [3:0] arr [0:3]);
        logic [7:0] sum = 0;
        for (int i = 0; i < 4; i++) begin
            sum += arr[i];
        end
        return sum;
    endfunction
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            register_q <= 4'b0;
            data_out_reg <= 4'b0;
            for (int i=0; i<4; i++) my_packed_array[i] <= 4'b0;
            for (int i=0; i<3; i++) begin
                for (int j=0; j<4; j++) my_unpacked_array[i][j] <= 8'b0;
            end
        end else begin
            register_q <= data_in;
            data_out_reg <= register_q;
            my_packed_array[0] <= data_in;
            my_packed_array[1] <= data_in + 1;
            my_packed_array[2] <= data_in + 2;
            my_packed_array[3] <= data_in + 3;
            my_unpacked_array[0][0] <= {data_in, data_in};
            my_unpacked_array[1][1] <= {data_in[2:0], 1'b1, data_in[3:0]};
        end
    end
    assign array_sum_out = calculate_sum(my_packed_array);
endmodule
module EnumStructTypedefs (
    input logic [1:0] operation_sel,
    input logic [7:0] data_val_a,
    input logic [7:0] data_val_b,
    output logic [7:0] result_out,
    output logic [2:0] current_state_enum
);
    typedef enum logic [2:0] {
        IDLE_ST,
        ADD_ST,
        SUB_ST,
        MUL_ST,
        DIV_ST,
        ERROR_ST
    } op_state_e;
    typedef struct packed {
        logic [7:0] operand1;
        logic [7:0] operand2;
        op_state_e  operation;
        logic       valid;
    } op_packet_s;
    op_state_e current_state;
    op_packet_s my_op_packet;
    task automatic process_op (input op_packet_s packet_in, output logic [7:0] result_out_task);
        case (packet_in.operation)
            ADD_ST: result_out_task = packet_in.operand1 + packet_in.operand2;
            SUB_ST: result_out_task = packet_in.operand1 - packet_in.operand2;
            MUL_ST: result_out_task = packet_in.operand1 * packet_in.operand2;
            DIV_ST: result_out_task = (packet_in.operand2 != 0) ? (packet_in.operand1 / packet_in.operand2) : 0;
            default: result_out_task = 8'hFF;
        endcase
    endtask
    always_comb begin
        my_op_packet.operand1 = data_val_a;
        my_op_packet.operand2 = data_val_b;
        my_op_packet.valid = 1'b1;
        case (operation_sel)
            2'b00: current_state = IDLE_ST;
            2'b01: current_state = ADD_ST;
            2'b10: current_state = SUB_ST;
            2'b11: current_state = MUL_ST;
            default: current_state = ERROR_ST;
        endcase
        my_op_packet.operation = current_state;
        process_op(my_op_packet, result_out);
        current_state_enum = current_state;
    end
endmodule
module SvClassesAndRandomization (
    input logic class_en,
    input logic [7:0] seed_val,
    input logic [7:0] data_for_class,
    output logic [15:0] class_sum_result,
    output logic [7:0] rand_val_output
);
    class MyDataProcessor;
        rand logic [7:0] rand_val;
        randc logic [7:0] cycle_rand_val;
        logic [7:0] input_data;
        logic [15:0] processed_sum;
        constraint c_rand_val { rand_val inside {[1:100]}; }
        constraint c_sum { processed_sum == input_data + rand_val + cycle_rand_val; }
        function new(logic [7:0] init_data);
            this.input_data = init_data;
            this.processed_sum = 0;
            void'(this.randomize());
        endfunction
        function void process_data();
            void'(this.randomize());
        endfunction
        function logic [15:0] get_sum();
            return processed_sum;
        endfunction
        function void set_input_data(logic [7:0] new_data);
            this.input_data = new_data;
        endfunction
    endclass : MyDataProcessor
    MyDataProcessor my_processor_obj;
    logic [15:0] local_sum_result;
    logic [7:0]  local_rand_val;
    always_comb begin
        if (class_en) begin
            if (my_processor_obj == null) begin
                my_processor_obj = new(data_for_class);
            end
            my_processor_obj.set_input_data(data_for_class);
            my_processor_obj.process_data(); 
            local_sum_result = my_processor_obj.get_sum();
            local_rand_val = my_processor_obj.rand_val;
        end else begin
            local_sum_result = 0;
            local_rand_val = 0;
        end
        class_sum_result = local_sum_result;
        rand_val_output = local_rand_val;
    end
endmodule
module AdvancedDataStructures (
    input logic clk,
    input logic rst_n,
    input logic [7:0] push_val,
    input logic pop_req,
    input logic [3:0] access_idx,
    output logic [7:0] front_val,
    output logic [7:0] accessed_val
);
    localparam QUEUE_DEPTH = 8;
    logic [7:0] my_queue_data [0:QUEUE_DEPTH-1];
    logic [3:0] head_ptr, tail_ptr;
    logic [3:0] queue_count;
    localparam DYN_ARRAY_SIZE = 4;
    logic [7:0] my_fixed_array [0:DYN_ARRAY_SIZE-1]; 
    logic [7:0] local_front_val = 0;
    logic [7:0] local_accessed_val = 0;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            head_ptr <= 0;
            tail_ptr <= 0;
            queue_count <= 0;
            for (int i=0; i<QUEUE_DEPTH; i++) my_queue_data[i] <= 0;
            for (int i=0; i<DYN_ARRAY_SIZE; i++) my_fixed_array[i] <= 0;
        end else begin
            if (push_val != 0 && queue_count < QUEUE_DEPTH) begin
                my_queue_data[tail_ptr] <= push_val;
                tail_ptr <= (tail_ptr == QUEUE_DEPTH-1) ? 0 : tail_ptr + 1;
                queue_count <= queue_count + 1;
            end
            if (pop_req && queue_count > 0) begin
                head_ptr <= (head_ptr == QUEUE_DEPTH-1) ? 0 : head_ptr + 1;
                queue_count <= queue_count - 1;
            end
            my_fixed_array[0] <= push_val;
            my_fixed_array[1] <= push_val + 1;
            my_fixed_array[2] <= push_val + 2;
            my_fixed_array[3] <= push_val + 3;
        end
    end
    always_comb begin
        logic [7:0] my_assoc_array_local [string]; 
        my_assoc_array_local["first"] = push_val;
        my_assoc_array_local["second"] = pop_req ? 8'hAA : 8'hBB;
        local_front_val = (queue_count == 0) ? 0 : my_queue_data[head_ptr];
        front_val = local_front_val;
        if (access_idx < DYN_ARRAY_SIZE) begin
            local_accessed_val = my_fixed_array[access_idx];
        end else begin
            if (my_assoc_array_local.exists("first")) begin
                local_accessed_val = my_assoc_array_local["first"];
            end else begin
                local_accessed_val = 8'hCC;
            end
        end
        accessed_val = local_accessed_val;
    end
endmodule
module AssertionExamples (
    input logic clk,
    input logic rst_n,
    input logic req,
    input logic ack,
    input logic [7:0] data_validity,
    output logic check_ok
);
    logic internal_state;
    logic [7:0] data_val;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            internal_state <= 1'b0;
            data_val <= 8'b0;
        end else begin
            internal_state <= req;
            data_val <= data_validity;
        end
    end
    property req_ack_property;
        @(posedge clk) (req |-> ##[1:2] ack);
    endproperty 
    assert property (req_ack_property);
    cover property (@(posedge clk) (data_val == 8'hAA));
    always_comb begin
        if (req && ack) begin
            assert (data_validity != 8'h00);
        end
        check_ok = (req && ack);
    end
    assume property (@(posedge clk) (rst_n |-> ##1 (!req || !ack)));
endmodule
interface my_simple_interface (input logic clk);
    logic [15:0] data;
    logic enable;
    logic valid;
    modport MASTER (
        output data,
        output enable,
        input valid
    );
    modport SLAVE (
        input data,
        input enable,
        output valid
    );
endinterface
module VirtualInterfaceUser (
    input logic clk,
    input logic master_enable,
    input logic [15:0] master_data,
    output logic slave_valid_out
);
    virtual my_simple_interface vif_handle;
    class VirtualIfData;
        logic [15:0] internal_data;
        function new(logic [15:0] init_data);
            internal_data = init_data;
        endfunction
    endclass
    VirtualIfData my_vif_data_obj;
    always_comb begin
        if (my_vif_data_obj == null) begin
            my_vif_data_obj = new(16'hAAAA);
        end
        slave_valid_out = master_enable && (my_vif_data_obj.internal_data != 0);
        if (vif_handle != null) begin
            vif_handle.data = my_vif_data_obj.internal_data;
            vif_handle.enable = master_enable;
        end
        my_vif_data_obj.internal_data = master_data;
    end
endmodule
module LoopConstructs (
    input logic [7:0] loop_iterations_in,
    input logic [7:0] initial_val_in,
    output logic [7:0] for_loop_sum,
    output logic [7:0] while_loop_val
);
    logic [7:0] sum_for = 0;
    logic [7:0] val_while = 0;
    always_comb begin
        int j;
        sum_for = 0;
        for (int i = 0; i < loop_iterations_in; i++) begin
            sum_for = sum_for + 1;
        end
        for_loop_sum = sum_for;
        val_while = initial_val_in;
        j = 0;
        while (val_while < 100 && j < 10) begin
            val_while = val_while + 1;
            j = j + 1;
        end
        while_loop_val = val_while;
    end
endmodule
module SignedArithmeticAndBitwise (
    input logic signed [7:0] in_signed_a,
    input logic signed [7:0] in_signed_b,
    input logic [7:0] in_unsigned_c,
    output logic signed [8:0] out_signed_add,
    output logic signed [8:0] out_signed_mul,
    output logic [7:0] out_bitwise_and,
    output logic [7:0] out_bitwise_or,
    output logic [7:0] out_reduction_xor,
    output logic [7:0] out_shl,
    output logic [7:0] out_shr
);
    assign out_signed_add = in_signed_a + in_signed_b;
    assign out_signed_mul = in_signed_a * in_signed_b;
    assign out_bitwise_and = in_unsigned_c & 8'hF0;
    assign out_bitwise_or = in_unsigned_c | 8'h0F;
    assign out_reduction_xor = ^in_unsigned_c;
    assign out_shl = in_unsigned_c << 2;
    assign out_shr = in_unsigned_c >> 1;
endmodule
module AdvancedParametersAndTypedefs (
    input logic [7:0] value_in,
    input logic [1:0] config_sel,
    output logic [7:0] result_val,
    output logic [2:0] status_code_out
);
    parameter ADDR_WIDTH = 4;
    localparam MAX_ADDR = (1 << ADDR_WIDTH) - 1;
    typedef struct {
        logic [ADDR_WIDTH-1:0] address;
        logic [7:0] data;
    } mem_entry_s;
    typedef enum logic [2:0] {
        CONFIG_A = 0,
        CONFIG_B = 1,
        CONFIG_C = MAX_ADDR % 3 + 2,
        ERROR_CONFIG
    } config_e;
    config_e current_config;
    mem_entry_s my_entry;
    always_comb begin
        my_entry.address = value_in[ADDR_WIDTH-1:0];
        my_entry.data = value_in;
        case (config_sel)
            2'b00: current_config = CONFIG_A;
            2'b01: current_config = CONFIG_B;
            2'b10: current_config = CONFIG_C;
            default: current_config = ERROR_CONFIG;
        endcase
        status_code_out = current_config;
        if (current_config == CONFIG_A) begin
            result_val = my_entry.data + my_entry.address;
        end else if (current_config == CONFIG_B) begin
            result_val = my_entry.data - my_entry.address;
        end else if (current_config == CONFIG_C) begin
            result_val = my_entry.data * 2;
        end else begin
            result_val = 8'hFF;
        end
    end
endmodule
