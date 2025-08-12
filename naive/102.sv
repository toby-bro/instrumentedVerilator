module ParamLogic #(
    parameter DATA_WIDTH = 16
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic [DATA_WIDTH-1:0] data_in,
    input  logic [1:0]       ctrl_op,
    output logic [DATA_WIDTH-1:0] data_out,
    output logic             status_flag
);
    logic [DATA_WIDTH-1:0] reg_data;
    logic                  local_status;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            reg_data <= {DATA_WIDTH{1'b0}};
            local_status <= 1'b0;
        end else begin
            case (ctrl_op)
                2'b00: reg_data <= data_in;
                2'b01: reg_data <= reg_data + 1;
                2'b10: reg_data <= reg_data << 1;
                default: reg_data <= data_in ^ reg_data;
            endcase
            local_status <= (reg_data == {DATA_WIDTH{1'b1}});
        end
    end
    assign data_out = reg_data;
    assign status_flag = local_status;
endmodule
module TypeExplorer (
    input  logic [7:0] in_val,
    input  logic [1:0] op_sel,
    output logic [15:0] out_struct_val,
    output logic [7:0] out_enum_val,
    output logic [7:0] array_sum,
    output int          queue_len
);
    typedef struct packed {
        logic [7:0] field_a;
        logic [7:0] field_b;
    } MyStruct_t;
    typedef enum logic [2:0] {
        STATE_IDLE = 3'b000,
        STATE_INIT = 3'b001,
        STATE_PROC = 3'b010,
        STATE_DONE = 3'b100
    } FSM_State_t;
    MyStruct_t       s_data;
    FSM_State_t      current_state;
    logic [7:0]      fixed_array[4];
    logic [7:0][3:0] packed_array;
    logic [7:0]      dynamic_array[];
    logic associative_map[int];
    int              int_queue[$];
    always_comb begin
        s_data.field_a = in_val;
        s_data.field_b = in_val + 1;
        out_struct_val = {s_data.field_a, s_data.field_b};
        case (op_sel)
            2'b00: current_state = STATE_IDLE;
            2'b01: current_state = STATE_INIT;
            2'b10: current_state = STATE_PROC;
            default: current_state = STATE_DONE;
        endcase
        out_enum_val = current_state;
    end
    always_comb begin
        int i;
        automatic logic [7:0] sum_val = 8'h00;
        for (i=0; i<4; i++) begin
            fixed_array[i] = in_val + i;
            sum_val += fixed_array[i];
        end
        array_sum = sum_val;
        packed_array = {16'h1234, 16'h5678};
        if (op_sel == 2'b00) begin
            dynamic_array = new[2];
            dynamic_array[0] = in_val;
            dynamic_array[1] = in_val + 1;
        end else if (op_sel == 2'b01) begin
            dynamic_array = new[3](dynamic_array);
            dynamic_array[2] = in_val + 2;
        end else begin
            dynamic_array = new[0];
        end
        if (op_sel == 2'b10) begin
            associative_map[1] = in_val[0];
            associative_map[2] = in_val[1];
        end else begin
            associative_map.delete();
        end
        int_queue.delete();
        if (op_sel == 2'b11) begin
            int_queue.push_back(in_val);
            int_queue.push_front(in_val + 1);
            int_queue.insert(1, in_val + 2);
        end
        queue_len = int_queue.size();
    end
endmodule
module FuncTaskLogic (
    input  logic [7:0] a,
    input  logic [7:0] b,
    input  logic       sel_func,
    input  logic       clk,
    input  logic       rst_n,
    output logic [7:0] result_func,
    output logic [7:0] result_task
);
    function automatic logic [7:0] calculate_val (input logic [7:0] val1, input logic [7:0] val2, input logic select);
        if (select) begin
            return val1 + val2;
        end else begin
            return val1 - val2;
        end
    endfunction
    task automatic update_result_task (input logic [7:0] val1, input logic [7:0] val2, output logic [7:0] out_val);
        out_val = val1 * val2;
        if (out_val > 100) begin
            out_val = out_val / 2;
        end
    endtask
    logic [7:0] internal_func_res;
    logic [7:0] internal_task_res;
    assign internal_func_res = calculate_val(a, b, sel_func);
    assign result_func = internal_func_res;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            internal_task_res <= 8'h00;
        end else begin
            update_result_task(a, b, internal_task_res);
        end
    end
    assign result_task = internal_task_res;
endmodule
module ClassProcessor (
    input  logic         clk,
    input  logic         rst_n,
    input  logic [15:0]  data_in,
    input  logic [1:0]   cmd,
    output logic         status_out,
    output logic [15:0]  proc_data_out
);
    class DataHandler;
        rand logic [15:0] internal_data;
        logic [15:0] processed_data;
        logic        error_flag;
        function new();
            internal_data = 16'h0000;
            processed_data = 16'h0000;
            error_flag = 1'b0;
        endfunction
        function void set_data(input logic [15:0] new_data);
            internal_data = new_data;
            error_flag = 1'b0;
        endfunction
        function void process();
            if (internal_data == 16'hFFFF) begin
                processed_data = 16'hAAAA;
                error_flag = 1'b1;
            end else begin
                processed_data = internal_data + 1;
                error_flag = 1'b0;
            end
        endfunction
        function logic [15:0] get_processed_data();
            return processed_data;
        endfunction
        function bit get_error_flag();
            return error_flag;
        endfunction
    endclass
    DataHandler my_handler;
    logic [15:0] current_proc_data;
    logic        current_status;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            if (my_handler != null) begin
                my_handler = null;
            end
            current_proc_data <= 16'h0000;
            current_status <= 1'b0;
        end else begin
            if (my_handler == null) begin
                my_handler = new();
            end
            case (cmd)
                2'b00: begin
                end
                2'b01: begin
                    my_handler.set_data(data_in);
                end
                2'b10: begin
                    my_handler.process();
                end
                default: begin
                    current_proc_data <= my_handler.get_processed_data();
                    current_status <= my_handler.get_error_flag();
                end
            endcase
        end
    end
    assign proc_data_out = current_proc_data;
    assign status_out = current_status;
endmodule
module GenerateExample #(parameter NUM_STAGES = 4, parameter bit SELECT_SUM_TYPE = 1) (
    input  logic [7:0] in_a,
    input  logic [7:0] in_b,
    input  logic       clk,
    input  logic       rst_n,
    output logic [7:0] out_sum,
    output logic [7:0] out_xor
);
    logic [7:0] internal_sum [NUM_STAGES];
    logic [7:0] internal_xor [NUM_STAGES];
    genvar i;
    generate
        for (i=0; i<NUM_STAGES; i=i+1) begin : stage_gen
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    internal_sum[i] <= 8'h00;
                    internal_xor[i] <= 8'h00;
                end else begin
                    if (i == 0) begin
                        internal_sum[i] <= in_a + in_b;
                        internal_xor[i] <= in_a ^ in_b;
                    end else begin
                        internal_sum[i] <= internal_sum[i-1] + i;
                        internal_xor[i] <= internal_xor[i-1] ^ i;
                    end
                end
            end
        end
    endgenerate
    generate
        if (SELECT_SUM_TYPE) begin : sum_output_gate
            assign out_sum = internal_sum[NUM_STAGES-1];
            assign out_xor = 8'h00;
        end else begin : xor_output_gate
            assign out_sum = 8'h00;
            assign out_xor = internal_xor[NUM_STAGES-1];
        end
    endgenerate
endmodule
module ComplexOperators (
    input  logic [7:0] data_in_a,
    input  logic [7:0] data_in_b,
    input  logic [1:0] op_mode,
    input  logic       cond_in,
    output logic [15:0] result_math,
    output logic        result_logic,
    output logic [7:0]  result_reduce,
    output logic [15:0] result_concat
);
    logic [7:0] temp_val;
    always_comb begin
        case (op_mode)
            2'b00: result_math = data_in_a + data_in_b;
            2'b01: result_math = data_in_a - data_in_b;
            2'b10: result_math = data_in_a * data_in_b;
            default: result_math = data_in_a / (data_in_b == 0 ? 1 : data_in_b);
        endcase
    end
    assign result_logic = (data_in_a > data_in_b) && (op_mode != 2'b00) || cond_in;
    assign temp_val = data_in_a | data_in_b;
    assign result_reduce = &temp_val ? temp_val : (~temp_val);
    assign result_concat = {data_in_a, data_in_b};
endmodule
