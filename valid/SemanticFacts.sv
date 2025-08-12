timeunit 1ns;
timeprecision 1ps;
interface bus_if (input bit clk);
    logic data;
    modport master (input clk, output data);
    modport slave  (input clk, input  data);
endinterface
typedef class ForwardC;
class ForwardC;
    int x;
endclass
virtual class iface_class;
    pure virtual function void dummy();
endclass
program automatic dummy_prog;
endprogram
module lifetime_demo #(
    parameter WIDTH = 8
) (
    input  logic [WIDTH-1:0] in_data,
    output logic [WIDTH-1:0] out_data
);
    timeunit 1ns;
    timeprecision 1ps;
    function automatic logic [WIDTH-1:0] plus_one(input logic [WIDTH-1:0] val);
        automatic logic [WIDTH-1:0] tmp;
        tmp      = val + 1;
        plus_one = tmp;
    endfunction
    function logic [WIDTH-1:0] counter();
        static logic [WIDTH-1:0] c = 0;
        c = c + 1;
        counter = c;
    endfunction
    always_comb begin : main_comb
        out_data = plus_one(in_data) ^ counter();
    end
endmodule
module direction_edge (
    input  logic clk,
    input  logic rst_n,
    input  logic din,
    output logic dout
);
    typedef enum logic [1:0] {S0 = 2'd0, S1 = 2'd1} state_t;
    state_t state, next;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= S0;
        else
            state <= next;
    end
    always_comb begin
        next = state;
        case (state)
            S0: if (din)  next = S1;
            S1: if (!din) next = S0;
        endcase
    end
    assign dout = (state == S1);
    always @(posedge clk) begin
        assert (state inside {S0, S1});
    end
    final begin
        $static_assert(1);
    end
endmodule
module block_kind_demo (
    input  logic a,
    output logic b
);
    logic t1, t2, t3;
    always @* begin : seq_block
        t1 = a;
    end
    always @* fork
        t2 = a & 1'b1;
    join;
    always @* fork
        t3 = a | 1'b0;
    join_any;
    assign b = t1 ^ t2 ^ t3;
endmodule
module strength_demo (
    input  wire in,
    output wire out
);
    wire w1;
    wire w2;
    assign (strong1, weak0) w1 = in;
    pullup  (weak1) p1 (w2);
    pulldown(weak0) p2 (w2);
    tran t1 (w1, w2);
    rtran t2 (w2, w1);
    assign out = w2;
endmodule
module clocking_demo (
    input  logic clk,
    input  logic data_in,
    output logic data_out
);
    logic data_reg;
    clocking cb @(posedge clk);
        input  posedge data_in;
        output data_reg;
    endclocking
    always_ff @(posedge clk) begin
        data_reg <= data_in;
    end
    assign data_out = data_reg;
endmodule
module timescale_demo (
    input  logic x,
    output logic y
);
    assign y = x;
endmodule
module edge_demo (
    input  logic clk,
    input  logic in_sig,
    output logic out_sig
);
    logic q;
    always @(edge in_sig) begin
        q <= ~q;
    end
    assign out_sig = q;
endmodule
