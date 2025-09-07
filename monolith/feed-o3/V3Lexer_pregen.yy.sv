module mod_basic(
    input  logic a,
    input  logic b,
    output logic y
);
    (* full_case, parallel_case *) logic internal_wire;
    assign internal_wire = a & b;
    assign y = ~internal_wire;
endmodule
module mod_always_ff(
    input  logic clk,
    input  logic rst_n,
    input  logic d,
    output logic q
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            q <= 1'b0;
        else
            q <= d;
    end
endmodule
module mod_generate#(
    parameter WIDTH = 4
)(
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i = i + 1) begin : genblk
            assign out[i] = in[i];
        end
    endgenerate
endmodule
module mod_unique(
    input  logic [1:0] sel,
    input  logic       a,
    input  logic       b,
    input  logic       c,
    input  logic       d,
    output logic       y
);
    always_comb begin
        unique case (sel)
            2'b00: y = a;
            2'b01: y = b;
            2'b10: y = c;
            default: y = d;
        endcase
    end
endmodule
module mod_types(
    input  logic clk,
    output logic done
);
    typedef enum logic [1:0] {IDLE = 2'd0, RUN = 2'd1, DONE = 2'd2} state_t;
    state_t state, next;
    always_comb begin
        unique case (state)
            IDLE: next = RUN;
            RUN : next = DONE;
            default: next = IDLE;
        endcase
    end
    always_ff @(posedge clk) begin
        state <= next;
    end
    assign done = (state == DONE);
endmodule
interface bus_if#(parameter WIDTH = 8);
    logic [WIDTH-1:0] data;
endinterface
module mod_bus(
    input  logic       clk,
    input  logic [7:0] in,
    output logic [7:0] out
);
    bus_if #(8) bus();
    always_comb begin
        bus.data = in;
        out      = bus.data;
    end
endmodule
module mod_assert(
    input  logic clk,
    input  logic a,
    output logic y
);
    assign y = a;
    property p_example;
        @(posedge clk) a |-> y;
    endproperty
    assert property(p_example);
endmodule
module mod_struct(
    input  logic [15:0] in_a,
    input  logic [15:0] in_b,
    output logic [31:0] out_mult
);
    typedef struct packed {
        logic [15:0] lo;
        logic [15:0] hi;
    } packed_t;
    packed_t val;
    always_comb begin
        val.lo   = in_a;
        val.hi   = in_b;
        out_mult = val.lo * val.hi;
    end
endmodule
module mod_ops(
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [15:0] y
);
    logic [7:0] shl;
    logic       eq_wild;
    assign shl     = a <<< 2;
    assign eq_wild = (a === 8'bx);
    assign y       = (shl ** 2) + {15'd0, eq_wild};
endmodule
module mod_clocking(
    input  logic clk,
    input  logic d,
    output logic q
);
    always_ff @(posedge clk) begin
        q <= d;
    end
endmodule
