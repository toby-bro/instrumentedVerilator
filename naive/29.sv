package utils_pkg;
    typedef enum logic [1:0] {IDLE = 2'b00, BUSY = 2'b01, DONE = 2'b10} state_e;
    typedef struct packed {
        logic [15:0] data;
        logic        last;
    } frame_t;
    class mult_class;
        function automatic logic [15:0] mult(input logic [7:0] x, y);
            mult = x * y;
        endfunction
    endclass
endpackage
module comb_and #(parameter WIDTH = 8)(
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic [WIDTH-1:0] y
);
    always_comb y = a & b;
endmodule
module arithmetic_unit #(parameter WIDTH = 8)(
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    input  logic             op,
    output logic [WIDTH-1:0] y
);
    always_comb begin
        if (op)
            y = a + b;
        else
            y = a - b;
    end
endmodule
module fsm_example(
    input  logic clk,
    input  logic rst_n,
    input  logic start,
    output logic done
);
    import utils_pkg::*;
    state_e current, next;
    always_comb begin
        next = current;
        case (current)
            IDLE : if (start) next = BUSY;
            BUSY :            next = DONE;
            DONE : if (!start) next = IDLE;
            default: next = IDLE;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            current <= IDLE;
        else
            current <= next;
    end
    assign done = (current == DONE);
endmodule
module class_usage #(parameter WIDTH = 8)(
    input  logic                   clk,
    input  logic [WIDTH-1:0]       in1,
    input  logic [WIDTH-1:0]       in2,
    output logic [WIDTH-1:0]       result
);
    import utils_pkg::*;
    always_ff @(posedge clk) begin
        mult_class m = new();
        result <= m.mult(in1[7:0], in2[7:0]);
    end
endmodule
module struct_handler(
    input  utils_pkg::frame_t frame_in,
    output logic [15:0]       data_out
);
    assign data_out = frame_in.data;
endmodule
module array_logic(
    input  logic       clk,
    input  logic [3:0] idx,
    input  logic [7:0] val,
    output logic [7:0] mem_out
);
    logic [7:0] mem_array [0:15];
    always_ff @(posedge clk) begin
        mem_array[idx] <= val;
    end
    always_comb begin
        mem_out = mem_array[idx];
    end
endmodule
