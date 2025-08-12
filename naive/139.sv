package MyUtilsPackage;
    class BaseCalculator;
        protected int internal_value;
        function new();
            internal_value = 0;
        endfunction
        virtual function int calculate(int a, int b);
            return a + b;
        endfunction
        function void set_internal_value(int val);
            internal_value = val;
        endfunction
        function int get_internal_value();
            return internal_value;
        endfunction
    endclass
    class Multiplier extends BaseCalculator;
        function new();
            super.new();
        endfunction
        virtual function int calculate(int a, int b);
            return a * b;
        endfunction
    endclass
    class Adder extends BaseCalculator;
        function new();
            super.new();
        endfunction
    endclass
endpackage
import MyUtilsPackage::*;
module LogicUnit (
    input logic         clk,
    input logic         rst_n,
    input logic [7:0]   data_in_m1,
    input logic [1:0]   sel_m1,
    output logic [7:0]  data_out_m1,
    output logic [2:0]  status_m1
);
    typedef enum logic [1:0] {
        STATE_IDLE = 2'b00,
        STATE_PROCESS = 2'b01,
        STATE_DONE = 2'b10
    } FSM_STATE_E;
    typedef struct packed {
        logic [3:0] crc;
        logic       valid;
    } PacketInfo_T;
    FSM_STATE_E current_state, next_state;
    PacketInfo_T packet_status_reg;
    logic [7:0] internal_reg;
    logic [7:0] temp_comb_out;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_state <= STATE_IDLE;
            internal_reg <= 8'h00;
            packet_status_reg <= '{crc: 4'h0, valid: 1'b0};
        end else begin
            current_state <= next_state;
            internal_reg <= temp_comb_out;
            packet_status_reg.valid <= (next_state == STATE_DONE);
            packet_status_reg.crc <= sel_m1;
        end
    end
    always_comb begin
        next_state = current_state;
        temp_comb_out = data_in_m1;
        status_m1 = 3'b000;
        case (current_state)
            STATE_IDLE: begin
                if (sel_m1 == 2'b01) begin
                    next_state = STATE_PROCESS;
                    status_m1 = 3'b001;
                end
            end
            STATE_PROCESS: begin
                temp_comb_out = data_in_m1 + internal_reg;
                if (sel_m1 == 2'b10) begin
                    next_state = STATE_DONE;
                    status_m1 = 3'b010;
                end
            end
            STATE_DONE: begin
                temp_comb_out = internal_reg ^ data_in_m1;
                if (sel_m1 == 2'b00) begin
                    next_state = STATE_IDLE;
                    status_m1 = 3'b100;
                end
            end
            default: begin
                next_state = STATE_IDLE;
                status_m1 = 3'b111;
            end
        endcase
    end
    assign data_out_m1 = (current_state == STATE_DONE) ? internal_reg : 8'hFF;
endmodule
module ArrayProcessor (
    input  logic         clk_m2,
    input  logic         rst_n_m2,
    input  logic [3:0]   index_in,
    input  logic [7:0]   val_in,
    input  logic [1:0]   operation_m2,
    output logic [7:0]   array_out_m2,
    output logic [15:0]  sum_out_m2,
    output logic         is_power_of_two_m2
);
    parameter DATA_WIDTH = 8;
    parameter ARRAY_DEPTH = 16;
    logic [DATA_WIDTH-1:0] my_array [ARRAY_DEPTH-1:0];
    logic [DATA_WIDTH-1:0] dynamic_array_q [$];
    logic [DATA_WIDTH-1:0] associative_mem [int];
    function automatic [15:0] calculate_array_sum(input logic [DATA_WIDTH-1:0] arr [ARRAY_DEPTH-1:0]);
        logic [15:0] total_sum = 0;
        for (int i = 0; i < ARRAY_DEPTH; i++) begin
            total_sum += arr[i];
        end
        return total_sum;
    endfunction
    task automatic write_array_element(input logic [3:0] idx, input logic [7:0] val);
        if (idx < ARRAY_DEPTH) begin
            my_array[idx] = val;
        end
    endtask
    function automatic logic check_power_of_two(input int num);
        if (num <= 0) return 1'b0;
        return (num & (num - 1)) == 0;
    endfunction
    always_ff @(posedge clk_m2 or negedge rst_n_m2) begin
        if (!rst_n_m2) begin
            for (int i = 0; i < ARRAY_DEPTH; i++) begin
                my_array[i] <= 8'h00;
            end
            dynamic_array_q = {};
            associative_mem.delete();
        end else begin
            case (operation_m2)
                2'b00: begin
                end
                2'b01: begin
                    write_array_element(index_in, val_in);
                    dynamic_array_q.push_back(val_in);
                    associative_mem[index_in] = val_in;
                end
                2'b10: begin
                end
                2'b11: begin
                end
            endcase
        end
    end
    always_comb begin
        logic [DATA_WIDTH-1:0] assoc_val;
        array_out_m2 = (index_in < ARRAY_DEPTH) ? my_array[index_in] : 8'hXX;
        sum_out_m2 = calculate_array_sum(my_array);
        is_power_of_two_m2 = check_power_of_two(val_in);
        if (associative_mem.exists(index_in)) begin
            assoc_val = associative_mem[index_in];
        end else begin
            assoc_val = 8'h00;
        end
    end
endmodule
module ClassProcessor (
    input  logic        clk_m3,
    input  logic        rst_n_m3,
    input  logic [1:0]  cmd_m3,
    input  int          data_m3,
    output logic [2:0]  status_m3,
    output int          result_m3
);
    BaseCalculator  calc_handle;
    Multiplier      multiplier_obj;
    Adder           adder_obj;
    typedef enum {
        IDLE_STATE,
        ADD_STATE,
        MULTIPLY_STATE,
        PROCESS_DONE
    } ProcState_E;
    ProcState_E current_proc_state, next_proc_state;
    int operand_a, operand_b;
    always_ff @(posedge clk_m3 or negedge rst_n_m3) begin
        if (!rst_n_m3) begin
            current_proc_state <= IDLE_STATE;
            result_m3 <= 0;
            calc_handle <= null;
            multiplier_obj <= null;
            adder_obj <= null;
        end else begin
            current_proc_state <= next_proc_state;
            if (current_proc_state == IDLE_STATE) begin
                if (cmd_m3 == 2'b01) begin
                    if (adder_obj == null) begin
                        adder_obj = new();
                        calc_handle = adder_obj;
                    end
                    operand_a = data_m3;
                    next_proc_state = ADD_STATE;
                end else if (cmd_m3 == 2'b10) begin
                    if (multiplier_obj == null) begin
                        multiplier_obj = new();
                        calc_handle = multiplier_obj;
                    end
                    operand_a = data_m3;
                    next_proc_state = MULTIPLY_STATE;
                end else begin
                    next_proc_state = IDLE_STATE;
                end
            end else if (current_proc_state == ADD_STATE) begin
                operand_b = data_m3;
                if (calc_handle != null) begin
                    result_m3 <= calc_handle.calculate(operand_a, operand_b);
                    calc_handle.set_internal_value(result_m3);
                end
                next_proc_state = PROCESS_DONE;
            end else if (current_proc_state == MULTIPLY_STATE) begin
                operand_b = data_m3;
                if (calc_handle != null) begin
                    result_m3 <= calc_handle.calculate(operand_a, operand_b);
                    calc_handle.set_internal_value(result_m3);
                end
                next_proc_state = PROCESS_DONE;
            end else if (current_proc_state == PROCESS_DONE) begin
                if (cmd_m3 == 2'b00) begin
                    next_proc_state = IDLE_STATE;
                    calc_handle <= null;
                    multiplier_obj <= null;
                    adder_obj <= null;
                end else begin
                    next_proc_state = PROCESS_DONE;
                end
            end
        end
    end
    always_comb begin
        status_m3 = 3'b000;
        case (current_proc_state)
            IDLE_STATE:     status_m3 = 3'b000;
            ADD_STATE:      status_m3 = 3'b001;
            MULTIPLY_STATE: status_m3 = 3'b010;
            PROCESS_DONE:   status_m3 = 3'b011;
            default:        status_m3 = 3'b111;
        endcase
    end
endmodule
module ConfigurableLogic (
    input  logic        clk_m4,
    input  logic        rst_n_m4,
    input  logic [1:0]  cfg_in_m4,
    input  logic [7:0]  data_m4,
    output logic [7:0]  out_m4,
    output logic        parity_m4
);
    localparam CFG_PASSTHROUGH = 2'b00;
    localparam CFG_INVERT      = 2'b01;
    localparam CFG_XOR_PREV     = 2'b10;
    localparam CFG_SHIFT       = 2'b11;
    logic [7:0] internal_data_reg;
    logic [7:0] next_internal_data;
    parameter ENABLE_PARITY = 1;
    always_ff @(posedge clk_m4 or negedge rst_n_m4) begin
        if (!rst_n_m4) begin
            internal_data_reg <= 8'h00;
        end else begin
            internal_data_reg <= next_internal_data;
        end
    end
    always_comb begin
        next_internal_data = data_m4;
        out_m4 = internal_data_reg;
        case (cfg_in_m4)
            CFG_PASSTHROUGH: begin
                next_internal_data = data_m4;
            end
            CFG_INVERT: begin
                next_internal_data = ~data_m4;
            end
            CFG_XOR_PREV: begin
                next_internal_data = data_m4 ^ internal_data_reg;
            end
            CFG_SHIFT: begin
                next_internal_data = {data_m4[6:0], data_m4[7]};
            end
            default: begin
                next_internal_data = 8'hXX;
            end
        endcase
        out_m4 = next_internal_data;
    end
    generate
        if (ENABLE_PARITY) begin : ParityGenBlock
            logic parity_temp;
            always_comb begin
                parity_temp = ^internal_data_reg;
            end
            assign parity_m4 = parity_temp;
        end else begin : NoParityGenBlock
            assign parity_m4 = 1'b0;
        end
    endgenerate
    parameter NUM_GATES = 4;
    logic [NUM_GATES-1:0] internal_signals_A;
    logic [NUM_GATES-1:0] internal_signals_B;
    generate
        for (genvar i = 0; i < NUM_GATES; i++) begin : gate_block
            assign internal_signals_B[i] = internal_signals_A[i] & data_m4[i];
        end
    endgenerate
    assign internal_signals_A = data_m4[NUM_GATES-1:0];
endmodule
