package MyTypesAndFunctions;
    typedef enum {
        MODE_A,
        MODE_B,
        MODE_C,
        MODE_D
    } operation_mode_e;
    function automatic int square(int val);
        return val * val;
    endfunction
    function automatic int power(int base, int exp);
        int result = 1;
        for (int i = 0; i < exp; i++) begin
            result *= base;
        end
        return result;
    endfunction
endpackage
module ModuleParametersAndArrays #(
    parameter int DATA_WIDTH = 8,
    parameter int ARRAY_DEPTH = 16,
    localparam int LOG2_ARRAY_DEPTH = $clog2(ARRAY_DEPTH)
) (
    input logic clk,
    input logic rst_n,
    input logic [DATA_WIDTH-1:0] data_in,
    input logic [LOG2_ARRAY_DEPTH-1:0] array_idx,
    output logic [DATA_WIDTH-1:0] data_out,
    output logic [DATA_WIDTH+3:0] array_sum_out
);
    logic [DATA_WIDTH-1:0] mem_array [ARRAY_DEPTH-1:0];
    logic [7:0][7:0] packed_matrix;
    logic [DATA_WIDTH-1:0] reg_data;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            reg_data <= '0;
            for (int i = 0; i < ARRAY_DEPTH; i++) begin
                mem_array[i] <= '0;
            end
        end else begin
            reg_data <= data_in;
            mem_array[array_idx] <= data_in;
        end
    end
    logic [DATA_WIDTH+3:0] sum;
    always_comb begin
        sum = '0;
        for (int i = 0; i < ARRAY_DEPTH; i++) begin
            sum += mem_array[i];
        end
        packed_matrix[0][0] = data_in[0];
        data_out = reg_data;
        array_sum_out = sum;
    end
endmodule
interface my_interface (input logic clk);
    logic        valid;
    logic [7:0]  data;
    modport master (output valid, output data);
    modport slave (input valid, input data);
endinterface
typedef enum logic [1:0] {
    STATE_IDLE,
    STATE_PROCESSING,
    STATE_DONE
} proc_state_e;
typedef struct packed {
    logic [15:0] id;
    logic [7:0]  tag;
} packet_info_t;
module ModuleStructEnumAndInterface (
    input  logic i_clk,
    input  logic i_valid,
    input  proc_state_e i_state_val,
    input  packet_info_t i_struct_data,
    output logic o_ready,
    output proc_state_e o_enum_val,
    output packet_info_t o_struct_data
);
    my_interface intf(.clk(i_clk));
    assign intf.valid = i_valid;
    assign intf.data = i_struct_data.tag; 
    packet_info_t s_internal_data;
    proc_state_e s_current_state;
    always_ff @(posedge i_clk) begin
        s_current_state <= i_state_val;
        s_internal_data.id <= i_struct_data.id + 1;
        s_internal_data.tag <= i_struct_data.tag * 2;
    end
    always_comb begin
        o_ready = intf.valid && (s_current_state == STATE_PROCESSING);
        o_enum_val = s_current_state;
        o_struct_data = s_internal_data;
    end
    function automatic logic [7:0] get_tag(packet_info_t p_info);
        return p_info.tag;
    endfunction
    logic [7:0] func_result;
    always_comb begin
        func_result = get_tag(s_internal_data);
    end
endmodule
class DataProcessor;
    int sum = 0;
    int count = 0;
    function void add_data(int data);
        sum += data;
        count++;
    endfunction
    function int get_sum();
        return sum;
    endfunction
    function int get_count();
        return count;
    endfunction
    function void reset();
        sum = 0;
        count = 0;
    endfunction
endclass
module ModuleClassesAndAssertions (
    input  logic clk_i,
    input  logic reset_n_i,
    input  int   data_value_i,
    output int   output_sum_o,
    output int   output_count_o
);
    DataProcessor dp_inst;
    typedef int int_hash_t[*];
    int_hash_t associative_array;
    initial begin
        dp_inst = new(); 
    end
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            if (dp_inst != null) begin
                dp_inst.reset();
            end
            associative_array.delete();
            output_sum_o <= 0;
            output_count_o <= 0;
        end else begin
            dp_inst.add_data(data_value_i);
            output_sum_o <= dp_inst.get_sum();
            output_count_o <= dp_inst.get_count();
            if (data_value_i > 0) begin
                associative_array[data_value_i] <= associative_array.exists(data_value_i) ? associative_array[data_value_i] + 1 : 1; 
            end
            fork
                begin
                    int temp_val;
                    temp_val = data_value_i * 2;
                end
                begin
                    int another_val;
                    another_val = data_value_i + 5;
                end
            join
        end
    end
    property data_always_positive_p;
        @(posedge clk_i) (data_value_i >= 0);
    endproperty
    assert property (data_always_positive_p);
endmodule
module ModuleGenerateAndMemory #(
    parameter MEM_SIZE = 256,
    parameter ADDR_WIDTH = $clog2(MEM_SIZE),
    parameter DATA_WIDTH_MEM = 32
) (
    input  logic clk_gen,
    input  logic rst_gen,
    input  logic [ADDR_WIDTH-1:0] addr_gen,
    input  logic [DATA_WIDTH_MEM-1:0] data_in_gen,
    input  logic en_gen,
    output logic [DATA_WIDTH_MEM-1:0] data_out_gen
);
    logic [DATA_WIDTH_MEM-1:0] main_mem [MEM_SIZE-1:0];
    always_ff @(posedge clk_gen or negedge rst_gen) begin 
        if (!rst_gen) begin
            for (int i = 0; i < MEM_SIZE; i++) begin
                main_mem[i] <= '0;
            end
            data_out_gen <= '0;
        end else begin
            if (en_gen) begin
                main_mem[addr_gen] <= data_in_gen;
                data_out_gen <= main_mem[addr_gen];
            end else begin
                data_out_gen <= main_mem[addr_gen];
            end
        end
    end
    genvar i;
    generate
        for (i = 0; i < 4; i++) begin : gen_counters
            logic [3:0] counter;
            always_ff @(posedge clk_gen or negedge rst_gen) begin 
                if (!rst_gen) begin
                    counter <= 4'b0;
                end else begin
                    counter <= counter + 1;
                end
            end
        end
    endgenerate
    generate
        if (DATA_WIDTH_MEM > 16) begin : wide_data_path
            logic [DATA_WIDTH_MEM-1:0] temp_reg;
            always_ff @(posedge clk_gen) begin 
                temp_reg <= data_in_gen;
            end
        end else begin : narrow_data_path
            logic [15:0] narrow_temp_reg;
            always_ff @(posedge clk_gen) begin 
                narrow_temp_reg <= data_in_gen[15:0];
            end
        end
    endgenerate
    task automatic calculate_checksum (input logic [DATA_WIDTH_MEM-1:0] data, output logic [7:0] checksum);
        checksum = '0;
        for (int k = 0; k < DATA_WIDTH_MEM; k++) begin
            checksum = checksum ^ data[k];
        end
    endtask
    logic [7:0] mem_checksum;
    always_comb begin
        calculate_checksum(main_mem[addr_gen], mem_checksum);
    end
endmodule
module ModuleComplexLogic (
    input  logic clk_comp,
    input  logic rst_comp,
    input  logic [31:0] val_a,
    input  logic [31:0] val_b,
    input  logic [2:0]  opcode,
    output logic [31:0] result_comp,
    output logic [3:0]  status_flags_comp
);
    logic [31:0] internal_result;
    logic        carry, zero, negative, overflow;
    always_comb begin
        internal_result = '0;
        carry = 1'b0;
        zero = 1'b0;
        negative = 1'b0;
        overflow = 1'b0;
        case (opcode)
            3'b000: begin
                {carry, internal_result} = val_a + val_b;
            end
            3'b001: begin
                {carry, internal_result} = val_a - val_b;
                carry = ~carry;
            end
            3'b010: begin
                internal_result = val_a & val_b;
            end
            3'b011: begin
                internal_result = val_a | val_b;
            end
            3'b100: begin
                internal_result = val_a ^ val_b;
            end
            3'b101: begin
                internal_result = val_a <<< val_b[4:0];
            end
            3'b110: begin
                internal_result = $signed(val_a) * $signed(val_b);
            end
            default: begin
                internal_result = 'x;
            end
        endcase
        zero = (internal_result == '0);
        negative = internal_result[31];
        if (opcode == 3'b000) begin
            overflow = ((val_a[31] == val_b[31]) && (val_a[31] != internal_result[31]));
        end else if (opcode == 3'b001) begin
            overflow = ((val_a[31] != val_b[31]) && (val_a[31] != internal_result[31]));
        end else begin
            overflow = 1'b0;
        end
        unique casez (opcode)
            3'b00?: begin
            end
            3'b01?: begin
            end
            3'b1??: begin
            end
            default: begin
            end
        endcase
        result_comp = internal_result;
        status_flags_comp = {carry, zero, negative, overflow};
    end
endmodule
module ModulePackagesAndCovergroup (
    input  logic clk_cg,
    input  logic rst_n_cg,
    input  logic [7:0] data_in_cg,
    input  MyTypesAndFunctions::operation_mode_e mode_cg,
    output logic [7:0] data_out_cg,
    output logic event_triggered_cg
);
    import MyTypesAndFunctions::*;
    logic [7:0] processed_data;
    logic [7:0] squared_val;
    logic [7:0] powered_val;
    int my_queue[$];
    event my_event;
    always_ff @(posedge clk_cg or negedge rst_n_cg) begin
        if (!rst_n_cg) begin
            processed_data <= '0;
            squared_val <= '0;
            powered_val <= '0;
            my_queue.delete();
            event_triggered_cg <= 1'b0;
        end else begin
            processed_data <= data_in_cg;
            squared_val <= square(data_in_cg);
            powered_val <= power(data_in_cg[3:0], 2);
            my_queue.push_back(data_in_cg);
            if (my_queue.size() > 5) begin
                my_queue.pop_front();
            end
            event_triggered_cg <= 1'b0;
            if (data_in_cg == 8'hAA) begin
                -> my_event;
                event_triggered_cg <= 1'b1;
            end
        end
    end
    always_comb begin
        case (mode_cg)
            MODE_A: data_out_cg = processed_data;
            MODE_B: data_out_cg = squared_val;
            MODE_C: data_out_cg = my_queue.size() > 0 ? my_queue[0] : '0;
            MODE_D: data_out_cg = powered_val;
            default: data_out_cg = 'x;
        endcase
    end
endmodule
