`define WIDTH 8
`define SOME_MACRO 42
/*---------------------------------------------------------------------
 Package at compilation-unit scope to allow $unit hierarchical access
 ---------------------------------------------------------------------*/
package global_pkg;
    parameter int GLOBAL_PARAM = 3;
endpackage
/*---------------------------------------------------------------------
 Module exercising a wide variety of punctuation tokens, operators,
 struct literals (token "'{"), unique / case keywords, etc.
 ---------------------------------------------------------------------*/
module tokens_mod #(parameter WIDTH = `WIDTH)
    (input  logic [WIDTH-1:0] a,
     input  logic [WIDTH-1:0] b,
     output logic [WIDTH-1:0] y);
    typedef struct packed {
        logic [WIDTH-1:0] fieldA;
        logic [WIDTH-1:0] fieldB;
    } s_t;
    localparam s_t INIT_VAL = '{fieldA: '0, fieldB: '1};
    always_comb begin : TOKENS_BLOCK
        unique case (a)
            default: y = (a ^ b) | INIT_VAL.fieldA;
        endcase
    end
endmodule
/*---------------------------------------------------------------------
 Module that defines and instantiates a class inside a procedural block,
 using always_ff, automatic class variables, and macro references.
 ---------------------------------------------------------------------*/
module class_mod
    (input  logic        clk,
     input  logic [7:0]  in_data,
     output logic [7:0]  out_data);
    class adder_c;
        function int add (int x, int y);
            return x + y;
        endfunction
    endclass
    always_ff @(posedge clk) begin
        automatic adder_c obj = new();
        out_data <= obj.add(in_data, `SOME_MACRO);
    end
endmodule
/*---------------------------------------------------------------------
 Module that exercises a variety of pre-processor directives (`define,
 `ifdef, `else, `undef) to drive directive handling in the lexer.
 ---------------------------------------------------------------------*/
module directive_mod
    (input  logic [7:0] din,
     output logic [7:0] dout);
`define LOCAL_CONST 5
`ifdef LOCAL_CONST
    localparam int LCONST = `LOCAL_CONST;
`else
    localparam int LCONST = 0;
`endif
    assign dout = din + LCONST;
`undef LOCAL_CONST
endmodule
/*---------------------------------------------------------------------
 Module referencing a compilation-unit identifier through $unit to drive
 system identifier keyword handling.
 ---------------------------------------------------------------------*/
module system_id_mod
    (input  logic [3:0] a,
     output logic [3:0] y);
    import global_pkg::*;
    assign y = a + $unit::global_pkg::GLOBAL_PARAM;
endmodule
/*---------------------------------------------------------------------
 Simple module using an enum cast to exercise additional keyword usage.
 ---------------------------------------------------------------------*/
module enum_mod
    (input  logic [1:0] sel,
     output logic       out);
    typedef enum logic [1:0] { IDLE = 2'b00, RUN = 2'b01, STOP = 2'b10 } state_t;
    state_t state;
    always_comb begin
        state = state_t'(sel);
        out   = (state == RUN);
    end
endmodule
