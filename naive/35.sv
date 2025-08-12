package util_pkg;
    typedef struct packed {
        logic [7:0]   id;
        logic [31:0]  data;
    } pkt_t;
endpackage
module arithmetic_unit #(
    parameter int WIDTH = 16
)(
    input  logic                   clk,
    input  logic [WIDTH-1:0]       a_i,
    input  logic [WIDTH-1:0]       b_i,
    input  logic                   add_sub_n_i,
    output logic [WIDTH:0]         result_o
);
    typedef struct packed {
        logic [WIDTH-1:0] op_a;
        logic [WIDTH-1:0] op_b;
        logic             add_n;
    } op_t;
    class math_helper;
        function automatic logic [WIDTH:0] do_add(input op_t s);
            return s.op_a + s.op_b;
        endfunction
        function automatic logic [WIDTH:0] do_sub(input op_t s);
            return s.op_a - s.op_b;
        endfunction
    endclass
    op_t                 op_reg;
    math_helper          h;
    initial begin
        h = new();
    end
    always_ff @(posedge clk) begin
        op_reg.op_a <= a_i;
        op_reg.op_b <= b_i;
        op_reg.add_n <= add_sub_n_i;
    end
    always_comb begin
        if (op_reg.add_n)
            result_o = h.do_add(op_reg);
        else
            result_o = h.do_sub(op_reg);
    end
endmodule
module fsm_controller (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        start_i,
    output logic        done_o
);
    typedef enum logic [1:0] {IDLE, BUSY, DONE} state_t;
    state_t state_q, state_d;
    class counter_c;
        int count;
        function new(); count = 0; endfunction
        function void inc(); count++; endfunction
    endclass
    counter_c c;
    initial c = new();
    always_comb begin
        state_d = state_q;
        unique case (state_q)
            IDLE: if (start_i) state_d = BUSY;
            BUSY:              state_d = DONE;
            DONE:              state_d = IDLE;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) state_q <= IDLE;
        else        state_q <= state_d;
    end
    assign done_o = (state_q == DONE);
    always_ff @(posedge clk) begin
        if (state_q == BUSY)
            c.inc();
    end
    property p_done_low_until_busy;
        @(posedge clk) disable iff (!rst_n)
            (state_q == IDLE) |-> !done_o until (state_q == DONE);
    endproperty
    assert property (p_done_low_until_busy);
endmodule
module packet_checker (
    input  logic             clk,
    input  util_pkg::pkt_t   pkt_i,
    output logic             valid_o
);
    typedef union packed {
        util_pkg::pkt_t s;
        logic [39:0]    flat;
    } pkt_u;
    pkt_u pkt_reg;
    class pkt_validator;
        rand bit [7:0] id_mask;
        function new(); id_mask = 8'hFF; endfunction
        function bit is_valid(input util_pkg::pkt_t p);
            return ((p.id & id_mask) == p.id);
        endfunction
    endclass
    pkt_validator pv;
    initial begin
        pv = new();
        void'(pv.randomize() with {id_mask inside {8'hFF, 8'h0F};});
    end
    covergroup cg_pkt @(posedge clk);
        coverpoint pkt_i.id;
        coverpoint pkt_i.data[3:0];
    endgroup
    cg_pkt cg = new();
    always_ff @(posedge clk) begin
        pkt_reg.s <= pkt_i;
        cg.sample();
    end
    always_comb begin
        valid_o = pv.is_valid(pkt_reg.s);
    end
endmodule
module generate_array #(
    parameter int W = 8,
    parameter int D = 4
)(
    input  logic                 clk,
    input  logic [W-1:0]         data_i,
    output logic [W-1:0]         data_o
);
    function automatic int pow2(input int n);
        return 1 << n;
    endfunction
    logic [W-1:0] mem   [0:D-1];
    logic [$clog2(D)-1:0] wr_ptr;
    logic [$clog2(D)-1:0] rd_ptr;
    always_ff @(posedge clk) begin
        mem[wr_ptr] <= data_i;
        wr_ptr <= wr_ptr + 1'b1;
        rd_ptr <= rd_ptr + 1'b1;
        data_o <= mem[rd_ptr];
    end
endmodule
