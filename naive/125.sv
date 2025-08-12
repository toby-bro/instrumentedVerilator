module SimpleLogic (
    input logic clk,
    input logic reset_n,
    input logic [7:0] in_data,
    output logic [7:0] out_data,
    output logic status_flag
);
    parameter DATA_WIDTH = 8;
    logic [DATA_WIDTH-1:0] reg_data;
    logic [DATA_WIDTH-1:0] comb_out;
    assign status_flag = (in_data > 8'd100) ? 1'b1 : 1'b0;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            reg_data <= {DATA_WIDTH{1'b0}};
        end else begin
            reg_data <= in_data;
        end
    end
    always_comb begin
        if (reg_data[0]) begin
            comb_out = reg_data + 1;
        end else begin
            comb_out = reg_data - 1;
        end
    end
    assign out_data = comb_out;
endmodule
module StateMachine (
    input logic clk,
    input logic reset_n,
    input logic start_signal,
    output logic done_signal,
    output logic [2:0] state_output
);
    typedef enum logic [2:0] {
        IDLE,
        STATE_A,
        STATE_B,
        STATE_C,
        FINISH
    } fsm_state_e;
    fsm_state_e current_state, next_state;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            current_state <= IDLE;
        end else begin
            current_state <= next_state;
        end
    end
    always_comb begin
        next_state = current_state;
        done_signal = 1'b0;
        case (current_state)
            IDLE: begin
                if (start_signal) begin
                    next_state = STATE_A;
                end
            end
            STATE_A: begin
                next_state = STATE_B;
            end
            STATE_B: begin
                next_state = STATE_C;
            end
            STATE_C: begin
                next_state = FINISH;
            end
            FINISH: begin
                done_signal = 1'b1;
                if (!start_signal) begin
                    next_state = IDLE;
                end
            end
            default: begin
                next_state = IDLE;
            end
        endcase
        state_output = current_state;
    end
endmodule
module FuncTaskStruct (
    input logic clk,
    input logic [7:0] data_in_a,
    input logic [7:0] data_in_b,
    input logic [1:0] cmd,
    output logic [15:0] result_out,
    output logic task_status
);
    typedef struct packed {
        logic [7:0] op1;
        logic [7:0] op2;
        logic [1:0] operation;
    } OperationArgs_s;
    OperationArgs_s current_op_args;
    function automatic logic [15:0] perform_operation(OperationArgs_s args);
        case (args.operation)
            2'b00: perform_operation = {8'b0, args.op1} + {8'b0, args.op2};
            2'b01: perform_operation = {8'b0, args.op1} - {8'b0, args.op2};
            2'b10: perform_operation = args.op1 * args.op2;
            default: perform_operation = 16'hFFFF;
        endcase
    endfunction
    task automatic set_status(input logic status);
        task_status = status;
    endtask
    logic [15:0] internal_result;
    always_comb begin
        current_op_args.op1       = data_in_a;
        current_op_args.op2       = data_in_b;
        current_op_args.operation = cmd;
        internal_result = perform_operation(current_op_args);
        if (internal_result > 16'd500) begin
            set_status(1'b1);
        end else begin
            set_status(1'b0);
        end
        result_out = internal_result;
    end
endmodule
module ArrayQueueHandler (
    input logic clk,
    input logic reset_n,
    input logic [7:0] push_data,
    input logic push_en,
    input logic pop_en,
    output logic [7:0] front_data,
    output logic queue_empty,
    output logic queue_full
);
    parameter MAX_Q_SIZE = 4;
    logic [7:0] fixed_mem [0:7];
    class DataStorage;
        logic [7:0] dynamic_array[];
        logic [7:0] assoc_map [string];
        logic [7:0] data_queue[$];
        parameter CLASS_MAX_Q_SIZE = 4;
        function new();
            dynamic_array = new [4];
            foreach (dynamic_array[i]) dynamic_array[i] = 8'h00;
            assoc_map.delete();
            data_queue.delete();
        endfunction
        function void do_push(input logic [7:0] data_val);
            if (data_queue.size() < CLASS_MAX_Q_SIZE) begin
                data_queue.push_back(data_val);
            end
            if (dynamic_array.size() > 0) begin
                dynamic_array[0] = data_val;
            end
            assoc_map["key1"] = data_val;
        endfunction
        function void do_pop();
            if (data_queue.size() > 0) begin
                data_queue.pop_front();
            end
        endfunction
        function logic [7:0] get_front();
            if (data_queue.size() > 0) return data_queue[0]; 
            return 8'b0;
        endfunction
        function logic is_queue_empty();
            return (data_queue.size() == 0);
        endfunction
        function logic is_queue_full();
            return (data_queue.size() >= CLASS_MAX_Q_SIZE);
        endfunction
        function int get_dynamic_array_size();
            return dynamic_array.size();
        endfunction
        function logic [7:0] get_dynamic_array_elem(input int idx);
            if (idx >= 0 && idx < dynamic_array.size()) return dynamic_array[idx];
            return 8'b0;
        endfunction
        function logic [7:0] get_assoc_map_elem(input string key);
            if (assoc_map.exists(key)) return assoc_map[key];
            return 8'b0;
        endfunction
    endclass
    DataStorage storage_obj;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            fixed_mem <= '{default: 8'h00};
            storage_obj = new();
        end else begin
            if (storage_obj == null) begin
                storage_obj = new();
            end
            fixed_mem[0] <= push_data;
            if (push_en) begin
                storage_obj.do_push(push_data);
            end
            if (pop_en) begin
                storage_obj.do_pop();
            end
        end
    end
    always_comb begin
        logic [7:0] temp_front_data;
        logic temp_queue_empty;
        logic temp_queue_full;
        int array_size;
        logic [7:0] temp_dyn_read_val;
        string s_key;
        logic [7:0] temp_assoc_read_val;
        if (storage_obj == null) begin
            temp_front_data = 8'b0;
            temp_queue_empty = 1'b1;
            temp_queue_full = 1'b0;
        end else begin
            temp_front_data = storage_obj.get_front();
            temp_queue_empty = storage_obj.is_queue_empty();
            temp_queue_full = storage_obj.is_queue_full();
            array_size = storage_obj.get_dynamic_array_size();
            temp_dyn_read_val = 8'h00; 
            if (array_size > 0) begin
                temp_dyn_read_val = storage_obj.get_dynamic_array_elem(0);
            end
            s_key = "key1";
            temp_assoc_read_val = storage_obj.get_assoc_map_elem(s_key);
        end
        front_data = temp_front_data;
        queue_empty = temp_queue_empty;
        queue_full = temp_queue_full;
    end
endmodule
module ClassExample (
    input logic clk,
    input logic reset_n,
    input logic set_val_en,
    input logic [7:0] input_val,
    output logic [7:0] class_data_out,
    output logic is_valid_output
);
    class MyDataPacket;
        local logic [7:0] m_data;
        logic m_valid;
        function new();
            m_data = 8'h00;
            m_valid = 1'b0;
        endfunction
        function void set_data(input logic [7:0] val);
            m_data = val;
            m_valid = 1'b1;
        endfunction
        function logic [7:0] get_data();
            return m_data;
        endfunction
        function logic is_valid();
            return m_valid;
        endfunction
        function void clear_data();
            m_data = 8'h00;
            m_valid = 1'b0;
        endfunction
    endclass
    MyDataPacket data_obj;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            data_obj = new();
            class_data_out <= data_obj.get_data();
            is_valid_output <= data_obj.is_valid();
        end else begin
            if (data_obj == null) begin
                data_obj = new();
            end
            if (set_val_en) begin
                data_obj.set_data(input_val);
            end else begin
                data_obj.clear_data();
            end
            class_data_out <= data_obj.get_data();
            is_valid_output <= data_obj.is_valid();
        end
    end
endmodule
module ParamArithmetic (
    input logic clk,
    input logic reset_n,
    input logic [15:0] operand_a,
    input logic [15:0] operand_b,
    input logic [1:0] select_op,
    output logic [16:0] result_val,
    output logic parity_check
);
    localparam EXTENDED_WIDTH = 17;
    logic [EXTENDED_WIDTH-1:0] intermediate_result;
    logic [15:0] a_signed, b_signed;
    assign a_signed = operand_a;
    assign b_signed = operand_b;
    always_comb begin
        intermediate_result = {EXTENDED_WIDTH{1'b0}};
        case (select_op)
            2'b00: begin
                intermediate_result = {1'b0, operand_a} + {1'b0, operand_b};
            end
            2'b01: begin
                intermediate_result = $signed({1'b0, operand_a}) - $signed({1'b0, operand_b});
            end
            2'b10: begin
                intermediate_result = {8'hFF, operand_a[7:0] & operand_b[7:0], 1'b0};
            end
            2'b11: begin
                intermediate_result = ~^({operand_a, operand_b});
            end
            default: begin
                intermediate_result = {EXTENDED_WIDTH{1'bX}};
            end
        endcase
        result_val = intermediate_result;
        parity_check = ^result_val;
    end
endmodule
module DataStructureHandler (
    input logic clk,
    input logic reset_n,
    input logic [7:0] input_data_a,
    input logic [7:0] input_data_b,
    input logic union_select,
    input int index_in,
    output logic [15:0] output_val,
    output logic [15:0] struct_sum
);
    typedef struct packed {
        logic [7:0] field_a;
        logic [7:0] field_b;
    } DataPair_s;
    typedef union packed {
        logic [15:0] int_val;
        struct packed {
            logic [7:0] byte_val_high;
            logic [7:0] byte_val_low;
        } byte_vals;
    } MyUnion_u;
    DataPair_s arrayOfStructs [0:3];
    MyUnion_u current_union_val;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            for (int i=0; i<4; i=i+1) begin
                arrayOfStructs[i].field_a <= 8'h00;
                arrayOfStructs[i].field_b <= 8'h00;
            end
        end else begin
            if (index_in >= 0 && index_in < 4) begin
                arrayOfStructs[index_in].field_a <= input_data_a;
                arrayOfStructs[index_in].field_b <= input_data_b;
            end
        end
    end
    always_comb begin
        logic [15:0] temp_output_val;
        logic [15:0] temp_struct_sum;
        if (!reset_n) begin
            temp_output_val = 16'h0000;
            temp_struct_sum = 16'h0000;
        end else begin
            if (union_select) begin
                current_union_val.byte_vals.byte_val_high = input_data_a;
                current_union_val.byte_vals.byte_val_low  = input_data_b;
                temp_output_val = current_union_val.int_val;
            end else begin
                current_union_val.int_val = {input_data_a, input_data_b};
                temp_output_val = {current_union_val.byte_vals.byte_val_high, current_union_val.byte_vals.byte_val_low};
            end
            temp_struct_sum = 16'h0000;
            for (int i=0; i<4; i=i+1) begin
                temp_struct_sum += {arrayOfStructs[i].field_a, 8'h00} + {arrayOfStructs[i].field_b, 8'h00};
            end
        end
        output_val = temp_output_val;
        struct_sum = temp_struct_sum;
    end
endmodule
