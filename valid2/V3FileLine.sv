`ifndef UNIQUE_FILE_GUARD
`define UNIQUE_FILE_GUARD
`define ADD(a,b) \
   ((a)  + \
   (b))
module m_line_directive (
    input  logic [7:0] in,
    output logic [7:0] out
);
    `line 42 "virtual1.vh" 0
    logic [7:0] tmp;
    assign tmp = in;
    `line 50 "virtual1.vh" 2
    assign out = tmp;
    `line 100 "virtual1.vh" 1
endmodule
module m_class_usage (
    input  logic        clk,
    input  logic [15:0] din,
    output logic [15:0] dout
);
    class pack;
        bit [15:0] data;
        function new(bit [15:0] d); data = d; endfunction
    endclass
    pack p;
    always_ff @(posedge clk) begin
        p = new(din);
        dout <= p.data;
    end
endmodule
module m_unused (
    input  logic i,
    output logic o
);
    /* verilator lint_off UNUSED */
    logic not_used1;
    logic not_used2;
    /* verilator lint_on  UNUSED */
    assign o = i;
endmodule
module m_struct_enum (
    input  logic [1:0]  sel,
    input  logic [31:0] in0,
    input  logic [31:0] in1,
    output logic [31:0] out
);
    typedef enum logic [1:0] {
        S0 = 2'd0,
        S1 = 2'd1,
        S2 = 2'd2,
        S3 = 2'd3
    } state_e;
    typedef struct packed {
        logic  [31:0] value;
        state_e       st;
    } packet_s;
    packet_s pk;
    always_comb begin
        pk.value = (sel == S0) ? in0 : in1;
        pk.st    = state_e'(sel);
        out      = pk.value;
    end
endmodule
module m_macro_multiline (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [8:0] sum
);
    assign sum = `ADD(a, b);
endmodule
`endif
