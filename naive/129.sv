module BasicCombinationalLogic (
    input  logic        in_a,
    input  logic        in_b,
    input  logic [7:0]  in_data,
    output logic        out_xor,
    output logic [7:0]  out_add,
    output logic [7:0]  out_mux
);
    parameter DATA_WIDTH = 8;
    logic [DATA_WIDTH-1:0] intermediate_val;
    assign out_xor = in_a ^ in_b;
    always_comb begin
        if (in_a) begin
            intermediate_val = in_data + {{DATA_WIDTH-1{1'b0}}, in_b};
        end else begin
            intermediate_val = in_data - {{DATA_WIDTH-1{1'b0}}, in_b};
        end
        out_add = intermediate_val;
    end
    always_comb begin
        case (in_a)
            1'b0: out_mux = in_data;
            1'b1: out_mux = ~in_data;
            default: out_mux = '0;
        endcase
    end
endmodule
module SimpleFSM (
    input  logic       clk,
    input  logic       reset_n,
    input  logic       start_signal,
    output logic       done_signal,
    output logic [1:0] state_out
);
    typedef enum logic [1:0] {
        IDLE,
        STATE1,
        STATE2,
        DONE
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
                    next_state = STATE1;
                end
            end
            STATE1: begin
                next_state = STATE2;
            end
            STATE2: begin
                next_state = DONE;
            end
            DONE: begin
                done_signal = 1'b1;
                if (!start_signal) begin
                    next_state = IDLE;
                end
            end
            default: begin
                next_state = IDLE;
            end
        endcase
        state_out = current_state;
    end
endmodule
module ArrayAndStructProcessor (
    input  logic [3:0][7:0] array_in,
    input  logic [7:0]      input_scalar,
    output logic [3:0][7:0] array_out,
    output logic [7:0]      sum_out
);
    typedef struct packed {
        logic [3:0] field_a;
        logic [3:0] field_b;
    } my_packed_struct_t;
    my_packed_struct_t struct_var;
    logic [7:0] packed_array [3:0];
    always_comb begin
        struct_var.field_a = array_in[0][3:0];
        struct_var.field_b = array_in[1][7:4];
        for (int i = 0; i < 4; i++) begin
            array_out[i] = array_in[i] + input_scalar;
        end
        sum_out = '0;
        for (int i = 0; i < 4; i++) begin
            packed_array[i] = array_in[i] + struct_var.field_a;
            sum_out = sum_out + packed_array[i];
        end
    end
endmodule
module FunctionTaskWrapper (
    input  logic [15:0] input_val1,
    input  logic [15:0] input_val2,
    input  logic        task_en,
    input  logic        clk,
    output logic [15:0] output_func_result,
    output logic [15:0] output_task_sum
);
    logic [15:0] task_internal_sum;
    function automatic logic [15:0] multiply_and_add(logic [15:0] a, logic [15:0] b);
        return (a * b) + 1;
    endfunction
    task automatic calculate_sum(input logic [15:0] op1, input logic [15:0] op2, output logic [15:0] result_sum);
        result_sum = op1 + op2 + 10;
    endtask
    always_comb begin
        output_func_result = multiply_and_add(input_val1, input_val2);
    end
    always_ff @(posedge clk) begin
        if (task_en) begin
            calculate_sum(input_val1, input_val2, task_internal_sum);
        end else begin
            task_internal_sum = '0;
        end
        output_task_sum <= task_internal_sum;
    end
endmodule
module ClassInstantiator (
    input  logic [7:0] class_input_a,
    input  logic [7:0] class_input_b,
    input  logic       trigger,
    output logic [7:0] class_output_result
);
    class MySimpleClass;
        rand logic [7:0] data_reg;
        function new();
            data_reg = 8'hAA;
        endfunction
        function logic [7:0] operate(logic [7:0] val1, logic [7:0] val2);
            data_reg = data_reg + val1;
            return data_reg + val2;
        endfunction
    endclass
    MySimpleClass my_instance;
    always_comb begin
        if (trigger) begin
            if (my_instance == null) begin
                my_instance = new();
            end
            class_output_result = my_instance.operate(class_input_a, class_input_b);
        end else begin
            class_output_result = '0;
        end
    end
endmodule
module GenerateBlockExample (
    input  logic [7:0] gen_in,
    input  logic       gen_select,
    output logic [7:0] gen_out,
    output logic [7:0] gen_sum
);
    localparam NUM_ELEMENTS = 4;
    logic [7:0] generated_data [NUM_ELEMENTS-1:0];
    logic [7:0] internal_sum = '0;
    genvar i;
    generate
        for (i = 0; i < NUM_ELEMENTS; i = i + 1) begin : gen_loop_block
            if (i % 2 == 0) begin : even_index
                assign generated_data[i] = gen_in + i;
            end else begin : odd_index
                assign generated_data[i] = gen_in - i;
            end
        end
    endgenerate
    assign gen_out = gen_select ? generated_data[NUM_ELEMENTS-1] : generated_data[0];
    always_comb begin
        internal_sum = '0;
        for (int k = 0; k < NUM_ELEMENTS; k++) begin
            internal_sum = internal_sum + generated_data[k];
        end
        gen_sum = internal_sum;
    end
endmodule
interface MySimpleInterface (input logic clk);
    logic [7:0] data;
    logic       valid;
    logic       ready;
    modport Master (output data, output valid, input ready);
    modport Slave  (input  data, input  valid, output ready);
endinterface
module InterfaceUser_Master (
    input  logic          clk,
    input  logic [7:0]    master_tx_data,
    input  logic          master_tx_valid,
    output logic [7:0]    master_rx_data,
    output logic          master_rx_ready
);
    MySimpleInterface master_if (.clk(clk));
    assign master_if.data  = master_tx_data;
    assign master_if.valid = master_tx_valid;
    assign master_rx_data  = master_if.data;
    assign master_rx_ready = master_if.ready;
    always_ff @(posedge clk) begin
        if (master_if.valid && master_if.ready) begin
        end
    end
endmodule
module InterfaceUser_Slave (
    input  logic          clk,
    input  logic [7:0]    slave_rx_data,
    input  logic          slave_rx_valid,
    output logic [7:0]    slave_tx_data,
    output logic          slave_tx_ready
);
    MySimpleInterface slave_if (.clk(clk));
    assign slave_if.data  = slave_rx_data;
    assign slave_if.valid = slave_rx_valid;
    assign slave_tx_data  = slave_if.data;
    assign slave_tx_ready = slave_if.ready;
    always_ff @(posedge clk) begin
        slave_if.ready <= slave_if.valid;
    end
endmodule
