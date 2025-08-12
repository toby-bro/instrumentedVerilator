interface bus_if #(parameter int WIDTH = 8) (input logic clk);
    logic [WIDTH-1:0] data;
    logic             valid;
    modport master (input data, valid);
    modport slave  (output data, valid);
endinterface
typedef enum logic [1:0] {
    IDLE = 2'd0,
    BUSY = 2'd1,
    DONE = 2'd2
} state_t;
typedef union packed {
    logic [7:0] raw;
    struct packed {
        logic [3:0] low;
        logic [3:0] high;
    } parts;
} byte_u;
class c_counter;
    int count;
    function new();
        count = 0;
    endfunction
    function void inc(int val);
        count += val;
    endfunction
    function int get();
        return count;
    endfunction
endclass
module bitwise_and #(
    parameter int WIDTH = 8
) (
    input  logic [WIDTH-1:0] in_a,
    input  logic [WIDTH-1:0] in_b,
    output logic [WIDTH-1:0] out_y
);
    assign out_y = in_a & in_b;
endmodule
module gen_vector #(
    parameter int WIDTH = 4
) (
    input  logic [WIDTH-1:0] vect_in,
    output logic [WIDTH-1:0] vect_out
);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : g_inv
            assign vect_out[i] = ~vect_in[i];
        end
    endgenerate
endmodule
module fsm_enum (
    input  logic clk,
    input  logic reset,
    input  logic start,
    output logic done
);
    state_t state, next;
    always_comb begin
        unique case (state)
            IDLE: next = start ? BUSY : IDLE;
            BUSY: next = DONE;
            DONE: next = IDLE;
            default: next = IDLE;
        endcase
    end
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            state <= IDLE;
        else
            state <= next;
    end
    assign done = (state == DONE);
endmodule
module nibble_extract (
    input  logic [7:0] in_byte,
    output logic [3:0] high_nibble
);
    always_comb begin
        byte_u u;
        u.raw       = in_byte;
        high_nibble = u.parts.high;
    end
endmodule
module class_counter (
    input  logic        clk,
    input  logic        reset,
    input  logic [7:0]  data_in,
    output logic [15:0] total_out
);
    c_counter counter;
    always_ff @(posedge clk) begin
        if (counter == null) counter = new();
        if (reset)
            counter = new();
        else
            counter.inc(data_in);
        total_out <= counter.get();
    end
endmodule
