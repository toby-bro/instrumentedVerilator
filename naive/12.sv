`default_nettype none
module arithmetic_ops (
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic [31:0] y,
    output logic        parity_o
);
    logic [31:0] tmp;
    always_comb begin
        tmp      = (a + b) - (a - b);
        y        = (tmp << 1) | (tmp >> 2);
        parity_o = ^y;
    end
endmodule
module packet_handler (
    input  logic [31:0] raw_in,
    output logic [31:0] raw_out
);
    typedef struct packed {
        logic [7:0]  header;
        logic [15:0] payload;
        logic [7:0]  footer;
    } packet_t;
    typedef union packed {
        packet_t     pkt;
        logic [31:0] raw;
    } packet_u;
    packet_u u_in, u_out;
    always_comb begin
        u_in.raw           = raw_in;
        u_out.pkt.header   = u_in.pkt.header + 8'h01;
        u_out.pkt.payload  = u_in.pkt.payload ^ 16'hA5A5;
        u_out.pkt.footer   = ~u_in.pkt.footer;
        raw_out            = u_out.raw;
    end
endmodule
module enum_fsm (
    input  logic clk,
    input  logic rst_n,
    input  logic start,
    output logic done
);
    typedef enum logic [1:0] {IDLE, RUN, DONE, ERROR} state_t;
    state_t state, next_state;
    always_comb begin
        next_state = state;
        case (state)
            IDLE   : if (start) next_state = RUN;
            RUN    :           next_state = DONE;
            DONE   :           next_state = IDLE;
            default:           next_state = ERROR;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next_state;
    end
    assign done = (state == DONE);
endmodule
module class_proc (
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic [31:0] sum
);
    class adder;
        int width;
        function new(int w); width = w; endfunction
        function automatic logic [31:0] do_add(logic [31:0] x, logic [31:0] y);
            return x + y;
        endfunction
    endclass
    always_comb begin
        automatic adder ad = new(32);
        sum = ad.do_add(a, b);
    end
endmodule
module param_generate #(
    parameter int WIDTH = 8,
    parameter int DEPTH = 4
) (
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);
    wire [WIDTH-1:0] mem [0:DEPTH-1];
    genvar i;
    generate
        for (i = 0; i < DEPTH; i++) begin : gen_blk
            assign mem[i] = data_in ^ {WIDTH{1'b1}};
        end
    endgenerate
    assign data_out = mem[0];
endmodule
module assertion_check (
    input  logic clk,
    input  logic [3:0] data,
    output logic pass
);
    property even_parity;
        @(posedge clk) (^data) == 1'b0;
    endproperty
    assert property (even_parity);
    assign pass = (^data) == 1'b0;
endmodule
`default_nettype wire
