module BasicCombinational (
    input logic [7:0] a_in,
    input logic [7:0] b_in,
    output logic [7:0] y_out
);
    logic [7:0] temp1;
    logic [7:0] temp2;
    assign temp1 = a_in & b_in;
    assign temp2 = a_in | b_in;
    assign y_out = (temp1 ^ temp2) + 8'd5;
endmodule
module SimpleSequential (
    input logic clk,
    input logic rst_n,
    input logic d_in,
    output logic q_out
);
    logic [3:0] counter_reg;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            q_out <= 1'b0;
            counter_reg <= 4'b0;
        end else begin
            q_out <= d_in;
            counter_reg <= counter_reg + 1'b1;
        end
    end
endmodule
module ProceduralCombAndEnum (
    input logic [1:0] sel_in,
    input logic data_en,
    input logic [7:0] data_a,
    input logic [7:0] data_b,
    output logic [7:0] result_out
);
    typedef enum logic [1:0] {
        STATE_IDLE,
        STATE_PROCESS_A,
        STATE_PROCESS_B,
        STATE_DONE
    } fsm_state_e;
    fsm_state_e current_state;
    always_comb begin
        result_out = 8'h00;
        current_state = STATE_IDLE;
        if (data_en) begin
            case (sel_in)
                2'b00: current_state = STATE_IDLE;
                2'b01: current_state = STATE_PROCESS_A;
                2'b10: current_state = STATE_PROCESS_B;
                default: current_state = STATE_DONE;
            endcase
            case (current_state)
                STATE_IDLE: result_out = 8'hAA;
                STATE_PROCESS_A: result_out = data_a;
                STATE_PROCESS_B: result_out = data_b;
                STATE_DONE: result_out = 8'hFF;
            endcase
        end else begin
            result_out = 8'h55;
        end
    end
endmodule
module StructAndParameterExample #(
    parameter DATA_WIDTH = 8
) (
    input logic [DATA_WIDTH-1:0] param_data_in,
    input logic [1:0] struct_sel_in,
    output logic [DATA_WIDTH-1:0] struct_data_out
);
    typedef struct packed {
        logic [DATA_WIDTH-1:0] value;
        logic enable;
    } my_data_s;
    my_data_s data_storage [4];
    always_comb begin
        for (int i=0; i<4; i++) begin
            data_storage[i].value = i + 1;
            data_storage[i].enable = (i % 2 == 0);
        end
        data_storage[struct_sel_in].value = param_data_in;
        data_storage[struct_sel_in].enable = 1'b1;
        struct_data_out = data_storage[struct_sel_in].value;
    end
endmodule
module ClassAndFunctionExample (
    input logic clk,
    input logic rst_n,
    input logic [7:0] val_in,
    output logic [7:0] processed_val_out
);
    class MyProcessor;
        rand int unsigned m_data;
        int unsigned m_processed_data;
        function new();
            m_data = 0;
            m_processed_data = 0;
        endfunction
        function int unsigned process_value(int unsigned input_val);
            m_data = input_val;
            m_processed_data = input_val * 2 + 1;
            return m_processed_data;
        endfunction
    endclass
    MyProcessor processor_inst;
    logic [7:0] temp_processed_data;
    function automatic logic [7:0] calculate_offset(logic [7:0] input_val);
        return input_val + 8'd10;
    endfunction
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            processed_val_out <= 8'h00;
            if (processor_inst != null) begin
                processor_inst = null;
            end
        end else begin
            if (processor_inst == null) begin
                processor_inst = new();
            end
            temp_processed_data = processor_inst.process_value(val_in);
            processed_val_out <= calculate_offset(temp_processed_data);
        end
    end
endmodule
module ArrayAndTaskExample (
    input logic [1:0] addr_in,
    input logic [3:0] write_data_in,
    input logic write_en,
    input logic [3:0] assoc_key_in,
    output logic [3:0] read_data_out,
    output logic [3:0] assoc_data_out
);
    logic [3:0] static_memory [4];
    logic [3:0] dynamic_array [];
    logic [3:0] assoc_memory [logic [3:0]];
    task automatic write_static_mem(input logic [1:0] addr, input logic [3:0] data);
        static_memory[addr] = data;
    endtask
    always_comb begin
        read_data_out = 4'h0;
        assoc_data_out = 4'h0;
        for (int i=0; i<4; i++) begin
            static_memory[i] = i;
        end
        if (write_en) begin
            write_static_mem(addr_in, write_data_in);
            assoc_memory[assoc_key_in] = write_data_in;
        end
        read_data_out = static_memory[addr_in];
        if (assoc_memory.exists(assoc_key_in)) begin
            assoc_data_out = assoc_memory[assoc_key_in];
        end else begin
            assoc_data_out = 4'hF; 
        end
    end
endmodule
module LoopAndAssertionExample (
    input logic [3:0] count_limit_in,
    input logic check_en,
    output logic [7:0] sum_out
);
    logic [7:0] current_sum;
    int i_loop;
    always_comb begin
        current_sum = 8'h00;
        for (i_loop = 0; i_loop < count_limit_in; i_loop++) begin
            current_sum += i_loop;
        end
        sum_out = current_sum;
        if (check_en) begin
            assert (current_sum < 8'd50) else begin
                $error("Assertion Failed: current_sum (%0d) exceeds limit!", current_sum);
            end
        end
    end
endmodule
module UnionExample (
    input logic select_in,
    input logic [15:0] input_val,
    output logic [15:0] output_val
);
    typedef union packed {
        logic [15:0] word;
        struct packed {
            logic [7:0] lo_byte;
            logic [7:0] hi_byte;
        } bytes;
    } my_union_u;
    my_union_u data_union;
    always_comb begin
        data_union.word = input_val;
        if (select_in == 1'b0) begin
            output_val = data_union.word;
        end else begin
            output_val = {data_union.bytes.lo_byte, data_union.bytes.hi_byte};
        end
    end
endmodule
module SignedOpsAndSlicing (
    input logic signed [7:0] s_a,
    input logic signed [7:0] s_b,
    input logic [15:0] u_data,
    output logic signed [8:0] s_sum,
    output logic [7:0] low_byte_out
);
    logic signed [7:0] product;
    logic [7:0] sliced_data;
    assign product = s_a * s_b;
    assign s_sum = s_a + s_b;
    assign sliced_data = u_data[7:0];
    assign low_byte_out = sliced_data;
endmodule
module PriorityUniqueCaseAndEvents (
    input logic [2:0] opcode_in,
    input logic       data_valid_in,
    input logic [7:0] data_in,
    output logic [7:0] result_out,
    output logic       op_done_out
);
    event operation_complete;
    always_comb begin
        op_done_out = 1'b0;
        result_out = 8'h00;
        unique case (opcode_in)
            3'b000: begin
                result_out = 8'hAA;
            end
            3'b001: begin
                result_out = data_in + 8'd1;
                op_done_out = 1'b1;
                -> operation_complete;
            end
            3'b010: begin
                result_out = data_in - 8'd1;
                op_done_out = 1'b1;
                -> operation_complete;
            end
            3'b011: begin
                if (data_valid_in) begin
                    result_out = data_in;
                    op_done_out = 1'b1;
                    -> operation_complete;
                end else begin
                    result_out = 8'hEE;
                end
            end
            3'b100: begin
                result_out = data_in << 1;
                op_done_out = 1'b1;
                -> operation_complete;
            end
            default: begin
                result_out = 8'hFF;
            end
        endcase
        if (opcode_in == 3'b110 && data_valid_in) begin
            result_out = data_in + 8'd7;
            op_done_out = 1'b1;
        end else if (opcode_in == 3'b111) begin
            result_out = data_in - 8'd7;
            op_done_out = 1'b1;
        end
    end
endmodule
