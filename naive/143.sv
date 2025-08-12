module CombinationalLogic (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    input logic         sel_op,
    output logic [8:0] out_result
);
    logic [7:0] temp_val1;
    logic [7:0] temp_val2;
    logic [8:0] add_res;
    logic [7:0] xor_res;
    assign temp_val1 = in_a + 1;
    assign temp_val2 = in_b - 1;
    always_comb begin
        add_res = temp_val1 + temp_val2;
        xor_res = temp_val1 ^ temp_val2;
        if (sel_op) begin
            out_result = add_res;
        end else begin
            out_result = {1'b0, xor_res};
        end
    end
endmodule
module SequentialLogic (
    input  logic         clk,
    input  logic         rst_n,
    input  logic [15:0]  data_in,
    output logic [15:0]  data_out
);
    logic [15:0]  q_reg;
    logic [15:0]  next_q;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            q_reg <= 16'h0000;
        end else begin
            q_reg <= next_q;
        end
    end
    always_comb begin
        if (data_in[0]) begin
            next_q = data_in + 1;
        end else begin
            next_q = data_in;
        end
    end
    assign data_out = q_reg;
endmodule
module TypeShowcase (
    input  logic [1:0]   operation_type,
    input  logic [7:0]   data_operand,
    output logic [15:0]  processed_data
);
    localparam OP_ADD = 2'b00;
    localparam OP_SUB = 2'b01;
    localparam OP_MUL = 2'b10;
    localparam OP_DIV = 2'b11;
    typedef enum logic [1:0] {
        STATE_IDLE,
        STATE_PROCESS,
        STATE_DONE,
        STATE_ERROR
    } fsm_state_e;
    fsm_state_e current_state;
    typedef struct packed {
        logic [7:0] input_val;
        logic [7:0] constant_val;
        logic [1:0] op_code;
    } control_packet_s;
    control_packet_s packet;
    logic [7:0] temp_array [3:0];
    logic [15:0] internal_result;
    always_comb begin
        packet.input_val    = data_operand;
        packet.constant_val = 8'd10;
        packet.op_code      = operation_type;
        for (int i=0; i<4; i++) begin
            temp_array[i] = data_operand + i;
        end
        current_state = STATE_IDLE;
        case (packet.op_code)
            OP_ADD: internal_result = packet.input_val + packet.constant_val + temp_array[0];
            OP_SUB: internal_result = packet.input_val - packet.constant_val - temp_array[1];
            OP_MUL: internal_result = packet.input_val * packet.constant_val + temp_array[2];
            OP_DIV: begin
                if (packet.constant_val != 0)
                    internal_result = packet.input_val / packet.constant_val + temp_array[3];
                else
                    internal_result = 16'hFFFF;
            end
            default: internal_result = 16'h0000;
        endcase
        if (internal_result > 100) begin
            current_state = STATE_PROCESS;
        end else begin
            current_state = STATE_DONE;
        end
        processed_data = internal_result;
    end
endmodule
module ClassDemonstration (
    input  logic         enable_calc,
    input  logic [7:0]   data_in_val,
    output logic [15:0]  class_output_val
);
    class MySimpleClass;
        rand int unsigned member_a;
        int unsigned member_b;
        function new(int unsigned val_b);
            member_b = val_b;
            member_a = 0;
        endfunction
        function automatic int unsigned calculate(int unsigned input_val);
            return (member_a + member_b + input_val);
        endfunction
        function automatic void set_member_a(int unsigned new_val);
            member_a = new_val;
        endfunction
    endclass
    MySimpleClass  my_object;
    logic [15:0]   local_result;
    always_comb begin
        my_object = new(100);
        my_object.set_member_a(data_in_val + 5);
        if (enable_calc) begin
            local_result = my_object.calculate(data_in_val);
        end else begin
            local_result = 0;
        end
        class_output_val = local_result;
    end
endmodule
module FunctionAndTask (
    input  logic [7:0]   val_a,
    input  logic [7:0]   val_b,
    input  logic         op_select,
    output logic [15:0]  func_result,
    output logic         task_status_out
);
    function automatic logic [15:0] calculate_operation(logic [7:0] operand1, logic [7:0] operand2, logic operation_type);
        if (operation_type == 0) begin
            return operand1 + operand2;
        end else begin
            return operand1 * operand2;
        end
    endfunction
    task automatic check_status(input logic [15:0] result, output logic status_ok);
        if (result > 200) begin
            status_ok = 1'b1;
        end else begin
            status_ok = 1'b0;
        end
    endtask
    logic [15:0] internal_func_result;
    logic        internal_task_status;
    always_comb begin
        internal_func_result = calculate_operation(val_a, val_b, op_select);
        check_status(internal_func_result, internal_task_status);
        func_result     = internal_func_result;
        task_status_out = internal_task_status;
    end
endmodule
module ArrayManipulation (
    input  logic [1:0]   index_in,
    input  logic [7:0]   data_write,
    output logic [7:0]   data_read_out
);
    logic [7:0] my_memory [3:0][7:0];
    typedef struct packed {
        logic [3:0] id;
        logic [3:0] item_type; 
    } metadata_s;
    metadata_s metadata_array [3:0];
    always_comb begin
        for (int i = 0; i < 4; i++) begin
            for (int j = 0; j < 8; j++) begin
                my_memory[i][j] = data_write + i + j;
            end
            metadata_array[i].id = i;
            metadata_array[i].item_type = (i % 2 == 0) ? 4'b0001 : 4'b0010;
        end
        if (index_in < 4) begin
            data_read_out = my_memory[index_in][index_in*2];
        end else begin
            data_read_out = 8'hFF;
        end
        foreach (my_memory[i]) begin
            automatic logic [7:0] temp_sum = 0;
            foreach (my_memory[i][j]) begin
                temp_sum += my_memory[i][j];
            end
        end
        foreach (metadata_array[k]) begin
            if (metadata_array[k].item_type == 4'b0010) begin
            end
        end
    end
endmodule
