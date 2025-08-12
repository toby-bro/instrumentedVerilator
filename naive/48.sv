package types_pkg;
    typedef enum logic[1:0] {IDLE, BUSY, DONE, ERR} state_e;
    typedef struct packed {
        logic [7:0]  byte0;
        logic [7:0]  byte1;
        logic [15:0] half;
    } word_s;
    function automatic [31:0] saturating_add(input [31:0] a, input [31:0] b);
        automatic logic [32:0] tmp;
        tmp = a + b;
        saturating_add = tmp[32] ? 32'hFFFF_FFFF : tmp[31:0];
    endfunction
endpackage
module param_adder #(parameter WIDTH = 8)
(
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic [WIDTH  :0] sum
);
    always_comb
        sum = {1'b0, a} + b;
endmodule
module simple_fsm
(
    input  logic clk,
    input  logic rst_n,
    input  logic start,
    output logic done
);
    import types_pkg::*;
    state_e state, next;
    always_comb begin
        unique case (state)
            IDLE :   next = start ? BUSY : IDLE;
            BUSY :   next = DONE;
            DONE :   next = IDLE;
            default: next = ERR;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next;
    end
    assign done = (state == DONE);
endmodule
module struct_unpacker
(
    input  logic [31:0] in_word,
    output logic [7:0]  out0,
    output logic [7:0]  out1,
    output logic [15:0] out2
);
    import types_pkg::*;
    always_comb begin
        word_s w_local;
        w_local = word_s'(in_word);
        out0 = w_local.byte0;
        out1 = w_local.byte1;
        out2 = w_local.half;
    end
endmodule
module priority_logic
(
    input  logic [3:0] req,
    output logic [1:0] grant
);
    always_comb begin
        priority if (req[3])       grant = 2'd3;
        else if (req[2])           grant = 2'd2;
        else if (req[1])           grant = 2'd1;
        else if (req[0])           grant = 2'd0;
        else                       grant = 2'd0;
    end
endmodule
module class_counter_module
(
    input  logic clk,
    input  logic rst_n,
    input  logic incr,
    output logic [31:0] count
);
    class counter_c;
        int unsigned value;
        function new(); value = 0; endfunction
        function void reset(); value = 0; endfunction
        function void inc();  value++; endfunction
        function int unsigned get(); return value; endfunction
    endclass
    counter_c c;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            c = new();
            count <= 0;
        end
        else begin
            if (c == null) c = new();
            if (incr) c.inc();
            count <= c.get();
        end
    end
endmodule
module parameterized_mux
#(
    parameter WIDTH = 8,
    parameter SEL   = 4
)
(
    input  logic [WIDTH-1:0] data [SEL-1:0],
    input  logic [$clog2(SEL)-1:0] index,
    output logic [WIDTH-1:0] out
);
    always_comb
        out = data[index];
endmodule
