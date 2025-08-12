package MyUtilityPackage;
    typedef enum {
        IDLE,
        PROCESSING,
        DONE,
        ERROR
    } EState;
    typedef enum logic [1:0] {
        ADD_OP = 2'b00,
        SUB_OP = 2'b01,
        MUL_OP = 2'b10,
        DIV_OP = 2'b11
    } EOpCode;
    typedef struct packed {
        logic       valid;
        logic [15:0] result;
        EState      status_state;
    } SResultData;
    function automatic int factorial(int n);
        int result = 1;
        for (int i = 1; i <= n; i++) begin
            result *= i;
        end
        return result;
    endfunction : factorial
    task automatic calculate_sum_and_diff(
        input int val1,
        input int val2,
        output int sum,
        output int diff
    );
        sum = val1 + val2;
        diff = val1 - val2;
    endtask : calculate_sum_and_diff
    function automatic logic [7:0] reverse_byte(logic [7:0] data);
        logic [7:0] reversed;
        for (int i = 0; i < 8; i++) begin
            reversed[i] = data[7-i];
        end
        return reversed;
    endfunction : reverse_byte
endpackage : MyUtilityPackage
import MyUtilityPackage::*;
module BasicLogic (
    input logic         clk,
    input logic         reset_n,
    input logic [7:0]   data_in,
    input logic         select,
    output logic [7:0]  data_out,
    output logic        status
);
    logic [7:0]         reg_data;
    logic [7:0]         comb_mux_out;
    logic               internal_status_sig;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            reg_data <= 8'h00;
        end else begin
            reg_data <= data_in;
        end
    end
    always_comb begin
        if (select) begin
            comb_mux_out = reg_data;
        end else begin
            comb_mux_out = data_in;
        end
    end
    assign data_out = comb_mux_out;
    always_comb begin
        internal_status_sig = (reg_data == data_in) && (data_in > 8'd10);
    end
    assign status = internal_status_sig;
endmodule
module TypeSystem (
    input logic [7:0]           input_val,
    input EOpCode               op_code,
    output SResultData          output_struct_data,
    output EState               output_enum_state
);
    logic [15:0] internal_result;
    EState       current_state;
    always_comb begin
        internal_result = 16'b0;
        current_state = IDLE;
        case (op_code)
            ADD_OP: begin
                internal_result = input_val + 16'd5;
                current_state = PROCESSING;
            end
            SUB_OP: begin
                internal_result = input_val - 16'd2;
                current_state = PROCESSING;
            end
            MUL_OP: begin
                internal_result = input_val * 16'd3;
                current_state = PROCESSING;
            end
            DIV_OP: begin
                if (input_val != 0) begin
                    internal_result = 16'd100 / input_val;
                    current_state = DONE;
                end else begin
                    internal_result = 16'hFFFF;
                    current_state = ERROR;
                end
            end
            default: begin
                current_state = ERROR;
            end
        endcase
        output_struct_data.valid        = (current_state != ERROR);
        output_struct_data.result       = internal_result;
        output_struct_data.status_state = current_state;
        output_enum_state = current_state;
    end
endmodule
module ClassAndMemory (
    input logic         clk,
    input logic         write_enable,
    input logic [7:0]   address,
    input logic [15:0]  write_data,
    output logic [15:0] read_data_out,
    output logic [31:0] class_result
);
    class MyDataProcessor;
        rand int m_val1;
        rand int m_val2;
        int      m_sum;
        constraint c_vals {
            m_val1 inside {[1:100]};
            m_val2 inside {[1:100]};
            m_val1 + m_val2 < 150;
        }
        function new();
        endfunction
        function int calculate_sum();
            m_sum = m_val1 + m_val2;
            return m_sum;
        endfunction
        function bit process_data(int data_in, ref int data_out);
            data_out = data_in * 2;
            return (data_in > 0);
        endfunction
    endclass : MyDataProcessor
    MyDataProcessor dp_inst;
    logic [15:0] my_ram_dynamic [];
    logic [7:0]  my_queue [$];
    logic [31:0] my_associative_array [string];
    logic [15:0] mem_read_data;
    logic [31:0] current_class_result;
    int          rand_gen_sum;
    always_comb begin
        automatic int processed_val;
        automatic bit success;
        if (dp_inst == null) begin
            dp_inst = new();
        end
        void'(dp_inst.randomize());
        rand_gen_sum = dp_inst.calculate_sum();
        current_class_result = rand_gen_sum + dp_inst.m_val1 + dp_inst.m_val2;
        success = dp_inst.process_data(10, processed_val);
        current_class_result += (success ? processed_val : 0);
    end
    always_ff @(posedge clk) begin
        automatic string current_key;
        if (my_ram_dynamic.size() == 0) begin
            my_ram_dynamic = new[256];
            my_queue.push_back(8'hAA);
            my_queue.push_back(8'hBB);
            my_associative_array["key1"] = 32'h12345678;
            my_associative_array["key2"] = 32'hABCDEF00;
        end
        if (write_enable) begin
            if (address < my_ram_dynamic.size()) begin
                my_ram_dynamic[address] = write_data;
            end
            if (my_queue.size() < 10) begin
                my_queue.push_front(address);
            end
            current_key = $sformatf("addr_%0d", address);
            my_associative_array[current_key] = {16'h0000, write_data};
        end
        if (address < my_ram_dynamic.size()) begin
            mem_read_data <= my_ram_dynamic[address];
        end else begin
            mem_read_data <= 16'hFFFF;
        end
    end
    assign read_data_out = mem_read_data;
    assign class_result = current_class_result;
endmodule
module PackageAndFunctions (
    input int           func_arg1,
    input int           func_arg2,
    input logic         task_trigger,
    output int          func_result,
    output logic [7:0]  byte_reversed,
    output int          task_status_sum,
    output int          task_status_diff
);
    int local_sum;
    int local_diff;
    int factorial_val;
    always_comb begin
        factorial_val = factorial(func_arg1);
    end
    always_comb begin
        if (task_trigger) begin
            calculate_sum_and_diff(func_arg1, func_arg2, local_sum, local_diff);
        end else begin
            local_sum = 0;
            local_diff = 0;
        end
        task_status_sum = local_sum;
        task_status_diff = local_diff;
    end
    assign byte_reversed = reverse_byte(func_arg2[7:0]);
    function automatic int multiply_by_const(input int val);
        return val * 10;
    endfunction : multiply_by_const
    assign func_result = factorial_val + multiply_by_const(func_arg2);
endmodule
module GenerateBlocks (
    input logic         clk,
    input logic         reset,
    input logic [7:0]   gen_input,
    input logic         config_select,
    output logic [7:0]  gen_output,
    output logic [7:0]  adder_sum
);
    parameter DATA_WIDTH = 8;
    parameter NUM_ADDERS = 4;
    logic [DATA_WIDTH-1:0] internal_data;
    logic [DATA_WIDTH-1:0] conditional_output;
    if (DATA_WIDTH == 8) begin : IfGenBlock_8bit
        localparam FACTOR = 2;
        always_comb begin
            conditional_output = gen_input * FACTOR;
        end
    end else begin : IfGenBlock_Other
        localparam FACTOR = 1;
        always_comb begin
            conditional_output = gen_input + FACTOR;
        end
    end
    assign gen_output = conditional_output;
    logic [DATA_WIDTH-1:0] adder_chain [NUM_ADDERS];
    logic [DATA_WIDTH-1:0] current_sum;
    genvar i;
    generate
        for (i = 0; i < NUM_ADDERS; i = i + 1) begin : AdderChain
            if (i == 0) begin
                always_comb begin
                    adder_chain[i] = gen_input + 1;
                end
            end else begin
                always_comb begin
                    adder_chain[i] = adder_chain[i-1] + 1;
                end
            end
        end
    endgenerate
    always_comb begin
        current_sum = adder_chain[NUM_ADDERS-1];
    end
    assign adder_sum = current_sum;
    logic [DATA_WIDTH-1:0] reg_config;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            reg_config <= '0;
        end else begin
            if (config_select) begin
                reg_config <= gen_input;
            end else begin
                reg_config <= conditional_output;
            end
        end
    end
endmodule
