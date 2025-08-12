package util_pkg;
  class parity_calc;
    function logic parity(logic [31:0] din);
      parity = ^din;
    endfunction
  endclass
endpackage
import util_pkg::*;
/*------------------------------------------------------------
 * 1. Arithmetic unit using parameterized widths
 *-----------------------------------------------------------*/
module arithmetic_unit #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic [WIDTH:0]   sum
);
    logic [WIDTH:0] result;
    always_comb begin
        result = a + b;
    end
    assign sum = result;
endmodule
/*------------------------------------------------------------
 * 2. Simple finite-state machine with enumerated states
 *-----------------------------------------------------------*/
module simple_fsm (
    input  logic clk,
    input  logic rst_n,
    input  logic start,
    output logic busy
);
    typedef enum logic [1:0] {IDLE, RUN, DONE} state_t;
    state_t state, next_state;
    always_comb begin
        next_state = state;
        unique case (state)
            IDLE: if (start) next_state = RUN;
            RUN :           next_state = DONE;
            DONE:           next_state = IDLE;
            default:        next_state = IDLE;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) state <= IDLE;
        else        state <= next_state;
    end
    assign busy = (state == RUN);
endmodule
/*------------------------------------------------------------
 * 3. Parity computation using a class, instantiated in an
 *    always_ff block (procedural instantiation)
 *-----------------------------------------------------------*/
module parity_with_class (
    input  logic        clk,
    input  logic [31:0] din,
    output logic        parity_out
);
    parity_calc pc;
    always_ff @(posedge clk) begin
        pc = new();
        parity_out <= pc.parity(din);
    end
endmodule
/*------------------------------------------------------------
 * 4. Packed struct manipulation
 *-----------------------------------------------------------*/
module struct_example (
    input  logic [15:0] in_data,
    output logic [7:0]  high_byte,
    output logic [7:0]  low_byte
);
    typedef struct packed {
        logic [7:0] low;
        logic [7:0] high;
    } word_t;
    word_t w;
    always_comb begin
        w         = in_data;
        high_byte = w.high;
        low_byte  = w.low;
    end
endmodule
/*------------------------------------------------------------
 * 5. Packed union with multi-dimensional packed array access
 *-----------------------------------------------------------*/
module union_example (
    input  logic [31:0] in_word,
    output logic [1:0]  nibble_xor
);
    typedef union packed {
        logic [31:0]       word;
        logic [3:0][7:0]   bytes;   
    } data_u;
    data_u u;
    always_comb begin
        u.word     = in_word;
        nibble_xor = u.bytes[0][1:0] ^ u.bytes[3][1:0];
    end
endmodule
/*------------------------------------------------------------
 * 6. Generate-block example with bitwise inversion
 *-----------------------------------------------------------*/
module gen_example #(
    parameter N = 4
) (
    input  logic [N-1:0] in_bus,
    output logic [N-1:0] out_bus
);
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : bit_loop
            assign out_bus[i] = ~in_bus[i];
        end
    endgenerate
endmodule
/*------------------------------------------------------------
 * 7. Assertion example demonstrating property specification
 *-----------------------------------------------------------*/
module assert_example (
    input  logic       clk,
    input  logic       enable,
    input  logic [7:0] data_in,
    output logic [7:0] data_out
);
    always_comb begin
        data_out = data_in;
    end
    property p_data_stable;
        @(posedge clk) disable iff (!enable)
            data_out == data_in;
    endproperty
    assert property (p_data_stable);
endmodule
