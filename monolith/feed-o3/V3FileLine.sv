package util_pkg;
    typedef enum logic [1:0] {ST_IDLE, ST_RUN, ST_DONE} state_e;
    class helper_c;
        function automatic logic [31:0] plus1 (input logic [31:0] v);
            return v + 1;
        endfunction
    endclass
endpackage
interface simple_bus_if (input logic clk);
    logic req;
    logic gnt;
    modport master (output req, input  gnt);
    modport slave  (input  req, output gnt);
endinterface
module mod_alpha (
    input  logic        clk,
    input  logic [7:0]  i,
    output logic [7:0]  o
);
    import util_pkg::*;
    localparam int UNUSED_PARAM = 32'hDEAD_BEEF;
`line 100 "virtual_alpha_lvl0.sv" 0
    state_e state = ST_IDLE;
    always_ff @(posedge clk) begin
        automatic helper_c h = new();
        o <= h.plus1(i);
    end
endmodule
module mod_beta #(
    parameter int WIDTH = 4
) (
    input  logic [WIDTH-1:0] a,
    input  logic             enable,
    output logic [WIDTH-1:0] y
);
`line `__LINE__ "virtual_beta_lvl1.sv" 1
`define ADD(X,Y) ((X) + (Y))
    always_comb begin
        y = enable ? `ADD(a, {WIDTH{1'b1}}) : {WIDTH{1'b0}};
    end
`undef ADD
endmodule
module mod_gamma (
    input  logic [31:0] bus_in,
    output logic [31:0] bus_out
);
    typedef struct packed {
        logic [7:0] byte0;
        logic [7:0] byte1;
        logic [7:0] byte2;
        logic [7:0] byte3;
    } bytes_t;
`line 200 "virtual_gamma_lvl2.svh" 2
    bytes_t b;
    always_comb begin
        b       = bytes_t'(bus_in);
        bus_out = {b.byte3, b.byte2, b.byte1, b.byte0};
    end
endmodule
module mod_delta #(
    parameter int COUNT = 8
) (
    input  logic [COUNT-1:0] in_bus,
    output logic [COUNT-1:0] out_bus
);
`line 300 "virtual_delta_gen.sv" 0
    genvar i;
    generate
        for (i = 0; i < COUNT; i = i + 1) begin : gen_blk
            assign out_bus[i] = ~in_bus[i];
        end
    endgenerate
endmodule
module mod_epsilon (
    input  logic        clk,
    input  logic        sel,
    input  logic [15:0] data_in,
    output logic [15:0] data_out
);
    typedef struct packed {
        logic [7:0] low;
        logic [7:0] high;
    } data_s;
    class adder16;
        function automatic logic [15:0] add1 (input logic [15:0] v);
            return v + 1;
        endfunction
    endclass
    data_s d;
    always_ff @(posedge clk) begin
        automatic adder16 a16 = new();
        if (sel) begin
            d.low  <= a16.add1(data_in)[7:0];
            d.high <= a16.add1(data_in)[15:8];
        end else begin
            d <= data_s'(data_in);
        end
        data_out <= {d.high, d.low};
    end
endmodule
module mod_zeta (
    input  logic dummy_in,
    output logic dummy_out
);
    localparam string FILE_NAME = `__FILE__;
    localparam int    LINE_NUM  = `__LINE__;
    assign dummy_out = dummy_in;
endmodule
module mod_eta #(
    parameter int N = 3
) (
    input  logic [N-1:0] x,
    output logic [N-1:0] y
);
    function automatic logic [N-1:0] rev (input logic [N-1:0] v);
`line 400 "virtual_eta_rev.sv" 1
        int idx;
        for (idx = 0; idx < N; idx = idx + 1) begin
            rev[idx] = v[N-1-idx];
        end
    endfunction
    assign y = rev(x);
endmodule
module mod_theta (
    input  logic a,
    output logic b
);
    logic unused_signal;
    assign b = a;
endmodule
module mod_iota (
    input  logic clk,
    input  logic rst_n,
    input  logic sig,
    output logic dummy
);
    property p_example;
        @(posedge clk) disable iff (!rst_n) sig |-> ##1 sig;
    endproperty
    assert property (p_example);
    assign dummy = sig;
endmodule
