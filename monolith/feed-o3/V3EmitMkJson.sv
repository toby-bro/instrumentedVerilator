package json_pkg;
    typedef enum logic [1:0] {IDLE = 2'd0, RUN = 2'd1, DONE = 2'd2, ERR = 2'd3} state_e;
    typedef struct packed {
        logic [7:0]  addr;
        logic [31:0] data;
    } trans_s;
    class helper;
        int sum;
        function new(int a, int b);
            sum = a + b;
        endfunction
    endclass
endpackage
interface bus_if (input bit clk);
    logic [7:0]  addr;
    logic [31:0] wdata;
    logic [31:0] rdata;
    logic        write;
    modport master (input  clk,
                    output addr,
                    output wdata,
                    output write,
                    input  rdata);
    modport slave  (input  clk,
                    input  addr,
                    input  wdata,
                    input  write,
                    output rdata);
endinterface
module json_struct #(parameter WIDTH = 32) (
    input  logic [WIDTH-1:0] in_data,
    output logic [WIDTH-1:0] out_data
);
    import json_pkg::*;
    function automatic int add_one(int a);
        helper h;
        h = new(a, 1);
        return h.sum;
    endfunction
    always_comb begin
        out_data = add_one(in_data);
    end
endmodule
module json_generate #(parameter N = 8) (
    input  logic [N-1:0] in_bus,
    output logic         parity
);
    logic [N-1:0] xor_chain;
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : gen_xor
            assign xor_chain[i] = in_bus[i];
        end
    endgenerate
    assign parity = ^xor_chain;
endmodule
module json_sm (
    input  logic clk,
    input  logic rst_n,
    output logic active
);
    import json_pkg::*;
    state_e state, nxt;
    always_comb begin
        nxt = state;
        unique case (state)
            IDLE : if (!rst_n) nxt = IDLE; else nxt = RUN;
            RUN  : nxt = DONE;
            DONE : nxt = ERR;
            ERR  : nxt = IDLE;
            default : nxt = IDLE;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) state <= IDLE;
        else        state <= nxt;
    end
    assign active = (state == RUN);
    property no_long_err;
        @(posedge clk) disable iff (!rst_n) (state == ERR) |-> ##1 (state != ERR);
    endproperty
    assert property (no_long_err);
endmodule
module json_bus_master (
    input  logic       clk,
    output logic [7:0]  addr,
    output logic [31:0] wdata,
    output logic        write,
    output logic        initiated
);
    logic [7:0] counter;
    always_ff @(posedge clk) begin
        addr    <= counter;
        wdata   <= counter + 32'h100;
        write   <= 1'b1;
        counter <= counter + 1;
    end
    assign initiated = write;
endmodule
module json_bus_slave (
    input  logic        clk,
    input  logic        write,
    input  logic [31:0] wdata,
    output logic [31:0] data_out
);
    always_ff @(posedge clk) begin
        if (write) data_out <= wdata;
    end
endmodule
module json_union (
    input  logic [31:0] in_word,
    output logic [7:0]  bytes [4]
);
    typedef union packed {
        logic [31:0] word;
        logic [3:0][7:0] bytes4;
    } word_u;
    word_u w;
    integer idx;
    always_comb begin
        w.word = in_word;
        for (idx = 0; idx < 4; idx = idx + 1) begin
            bytes[idx] = w.bytes4[idx];
        end
    end
endmodule
module json_math (
    input  logic signed [15:0] a,
    input  logic signed [15:0] b,
    output logic signed [31:0] prod
);
    assign prod = a * b;
endmodule
module json_conditional #(parameter USE_ADD = 1) (
    input  logic [7:0] x,
    input  logic [7:0] y,
    output logic [7:0] z
);
    generate
        if (USE_ADD) begin : add_blk
            assign z = x + y;
        end else begin : sub_blk
            assign z = x - y;
        end
    endgenerate
endmodule
module json_coverage (
    input  logic       clk,
    input  logic [3:0] sig,
    output logic       dummy
);
    assign dummy = sig[0];
    covergroup cg @(posedge clk);
        cp : coverpoint sig;
    endgroup
    cg cg_inst;
    always_ff @(posedge clk) begin
        cg_inst.sample();
    end
endmodule
module json_latch (
    input  logic en,
    input  logic d,
    output logic q
);
    always_latch begin
        if (en) q = d;
    end
endmodule
