package common_pkg;
    typedef enum logic [1:0] {IDLE, RUN, DONE} state_e;
    typedef struct packed {
        logic [3:0] nibble0;
        logic [3:0] nibble1;
    } nibbles_t;
endpackage
interface simple_if #(parameter int W = 8) (input logic clk);
    logic [W-1:0] data;
    modport producer (input  clk, output data);
    modport consumer (input  clk, input  data);
endinterface
module simple_adder #(
    parameter int WIDTH = 8
)(
    input  logic [WIDTH-1:0] in0,
    input  logic [WIDTH-1:0] in1,
    output logic [WIDTH:0]   out
);
    class adder_cls;
        logic [WIDTH-1:0] temp;
        function new();
        endfunction
    endclass
    adder_cls a_inst;
    always_comb out = in0 + in1;
    initial a_inst = new();
endmodule
module state_machine_demo(
    input  logic clk,
    input  logic rst_n,
    input  logic en,
    output logic done
);
    import common_pkg::*;
    state_e state, next;
    always_comb begin
        next = state;
        case (state)
            IDLE:  if (en) next = RUN;
            RUN:          next = DONE;
            DONE: if (!en) next = IDLE;
            default:      next = IDLE;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next;
    end
    assign done = (state == DONE);
    class sm_cls;
        state_e history[$];
        function new();
        endfunction
    endclass
    sm_cls smi;
    initial smi = new();
endmodule
module struct_union_demo(
    input  logic [7:0]  din,
    output logic [15:0] dout
);
    import common_pkg::*;
    typedef union packed {
        nibbles_t        nb;
        logic     [7:0]  raw8;
    } data_u;
    data_u u;
    always_comb begin
        u.raw8 = din;
        dout   = {u.nb.nibble1, u.nb.nibble0};
    end
    class struct_cls;
        logic [7:0] placeholder;
        function new();
        endfunction
    endclass
    struct_cls sc;
    initial sc = new();
endmodule
module generate_demo #(
    parameter int N = 4
)(
    input  logic [N-1:0] a,
    output logic [N-1:0] y
);
    genvar i;
    for (i = 0; i < N; i++) begin : g_inv
        assign y[i] = ~a[i];
    end
    class gen_cls;
        function new();
        endfunction
    endclass
    gen_cls gc;
    initial gc = new();
endmodule
module if_consumer #(
    parameter int W = 8
)(
    input  logic             clk,
    input  logic [W-1:0]     in_data,
    output logic [W-1:0]     q
);
    simple_if #(.W(W)) bus(clk);
    always_comb bus.data = in_data;
    always_ff @(posedge bus.clk) begin
        q <= bus.data;
    end
    class if_cls;
        function new();
        endfunction
    endclass
    if_cls ic;
    initial ic = new();
endmodule
