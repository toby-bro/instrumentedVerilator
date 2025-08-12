module CombinationalLogic (
    input  logic [7:0] a_in,
    input  logic [7:0] b_in,
    input  logic [1:0] sel_in,
    output logic [8:0] sum_out,
    output logic [7:0] logic_out,
    output logic       overflow_out
);
    localparam ADD_SEL = 2'b00;
    localparam OR_SEL  = 2'b01;
    localparam XOR_SEL = 2'b10;
    localparam NOT_SEL = 2'b11;
    logic [7:0] internal_val;
    assign sum_out = a_in + b_in;
    assign overflow_out = (a_in[7] == b_in[7]) && (sum_out[8] != a_in[7]);
    always_comb begin
        case (sel_in)
            ADD_SEL: logic_out = a_in & b_in;
            OR_SEL:  logic_out = a_in | b_in;
            XOR_SEL: logic_out = a_in ^ b_in;
            NOT_SEL: logic_out = ~a_in;
            default: logic_out = 8'hXX;
        endcase
        internal_val = (a_in > b_in) ? a_in : b_in;
    end
endmodule
module SequentialLogic (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        en_in,
    input  logic [15:0] data_in,
    output logic [15:0] data_out
);
    logic [15:0] internal_reg;
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            internal_reg <= 16'h0000;
        end else if (en_in) begin
            internal_reg <= data_in;
        end
    end
    assign data_out = internal_reg;
endmodule
module MemoryBlock (
    input  logic        clk,
    input  logic [7:0]  addr_in,
    input  logic        wr_en_in,
    input  logic [31:0] data_wr_in,
    output logic [31:0] data_rd_out
);
    logic [31:0] mem [255:0];
    assign data_rd_out = mem[addr_in];
    always_ff @(posedge clk) begin
        if (wr_en_in) begin
            mem[addr_in] <= data_wr_in;
        end
    end
endmodule
module AdvancedDataTypes (
    input  logic [7:0]  input_val,
    input  logic [3:0]  op_code,
    output logic [15:0] result_out
);
    typedef enum bit [1:0] {
        ADD_OP,
        SUB_OP,
        MUL_OP,
        DIV_OP
    } Operation_t;
    typedef struct packed {
        logic [7:0] val1;
        logic [7:0] val2;
    } Pair_t;
    typedef union packed {
        logic [15:0] word_value;
        Pair_t       pair_of_bytes;
    } WordOrPair_t;
    Operation_t current_op;
    Pair_t      input_pair;
    WordOrPair_t calc_result_union;
    class Calculator;
        logic [15:0] internal_result;
        function new();
            internal_result = 0;
        endfunction
        function automatic logic [15:0] perform_op(Pair_t pair_in, Operation_t op_in);
            case (op_in)
                ADD_OP: internal_result = pair_in.val1 + pair_in.val2;
                SUB_OP: internal_result = pair_in.val1 - pair_in.val2;
                MUL_OP: internal_result = pair_in.val1 * pair_in.val2;
                DIV_OP: begin
                    if (pair_in.val2 != 0) internal_result = pair_in.val1 / pair_in.val2;
                    else internal_result = 16'hDEAD;
                end
                default: internal_result = 0;
            endcase
            return internal_result;
        endfunction
    endclass
    Calculator my_calc_obj;
    always_comb begin
        input_pair.val1 = input_val;
        input_pair.val2 = input_val / 2;
        case (op_code)
            4'b0000: current_op = ADD_OP;
            4'b0001: current_op = SUB_OP;
            4'b0010: current_op = MUL_OP;
            4'b0011: current_op = DIV_OP;
            default: current_op = ADD_OP;
        endcase
        my_calc_obj = new();
        calc_result_union.word_value = my_calc_obj.perform_op(input_pair, current_op);
        result_out = calc_result_union.word_value;
    end
endmodule
module ParameterizedLogic #(
    parameter int DATA_WIDTH = 8,
    parameter int THRESHOLD  = 128
) (
    input  logic [DATA_WIDTH-1:0] in_data,
    output logic [DATA_WIDTH-1:0] out_data,
    output logic                   is_above_threshold
);
    logic [DATA_WIDTH-1:0] inverted_data;
    assign inverted_data = ~in_data;
    assign is_above_threshold = (in_data > THRESHOLD);
    assign out_data = (is_above_threshold) ? inverted_data : in_data;
endmodule
interface BusInterface (input logic clk);
    logic        valid;
    logic        ready;
    logic [31:0] data;
    modport Master (output valid, output data, input ready, input clk);
    modport Slave (input valid, input data, output ready, input clk);
endinterface
module InterfaceUser (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        valid_in,
    input  logic [31:0] data_in,
    output logic        ready_out,
    output logic [31:0] processed_data_out
);
    logic [31:0] internal_data_reg;
    logic        internal_ready;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            internal_data_reg <= 32'h0;
            internal_ready    <= 1'b0;
        end else begin
            if (valid_in && internal_ready) begin
                internal_data_reg <= data_in + 1;
                internal_ready    <= 1'b0;
            end else if (!valid_in) begin
                internal_ready    <= 1'b1;
            end
        end
    end
    assign ready_out          = internal_ready;
    assign processed_data_out = internal_data_reg;
endmodule
module FunctionTaskModule (
    input  logic [7:0] operand1,
    input  logic [7:0] operand2,
    input  logic       is_signed_mult,
    output logic [15:0] func_result,
    output logic [15:0] task_sum_result
);
    function automatic logic [15:0] multiply_unsigned(logic [7:0] a, logic [7:0] b);
        return a * b;
    endfunction
    function automatic logic [15:0] multiply_signed(logic [7:0] a, logic [7:0] b);
        return $signed(a) * $signed(b);
    endfunction
    task automatic calculate_sum(input logic [7:0] in1, input logic [7:0] in2, output logic [15:0] sum_out_task);
        sum_out_task = in1 + in2;
    endtask
    logic [15:0] internal_task_sum;
    always_comb begin
        if (is_signed_mult) begin
            func_result = multiply_signed(operand1, operand2);
        end else begin
            func_result = multiply_unsigned(operand1, operand2);
        end
        calculate_sum(operand1, operand2, internal_task_sum);
        task_sum_result = internal_task_sum;
    end
endmodule
