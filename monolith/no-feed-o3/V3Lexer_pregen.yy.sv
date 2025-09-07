module logic_cov(
    input  logic clk,
    input  logic rst_n,
    input  logic in_sig,
    output logic out_sig
);
    always_ff @(posedge clk) begin
        if (!rst_n)
            out_sig <= 1'b0;
        else
            out_sig <= in_sig;
    end
    covergroup cg @(posedge clk);
        option.per_instance = 1;
        COVER: coverpoint in_sig {
            bins zero = {0};
            bins one  = {1};
        }
    endgroup
    cg cg_inst = new();
endmodule
module enum_struct(
    input  logic a,
    input  logic b,
    output logic [3:0] y
);
    typedef enum logic [1:0] {IDLE, RUN, DONE, ERR} state_t;
    typedef struct packed {
        logic  [3:0] data;
        state_t      st;
    } packet_t;
    packet_t pkt;
    always_comb begin
        pkt.data = {3'b0, a};
        pkt.st   = b ? RUN : IDLE;
        y        = pkt.data;
    end
endmodule
module generate_case #(
    parameter int WIDTH = 8
) (
    input  logic [WIDTH-1:0] in_bus,
    output logic             parity
);
    generate
        if (WIDTH % 2 == 0) begin : even_width
            assign parity = ^in_bus;
        end
        else begin : odd_width
            assign parity = ~(^in_bus);
        end
    endgenerate
endmodule
interface simple_if(input logic clk);
    logic data;
    modport master (input  clk, output data);
    modport slave  (input  clk, input  data);
endinterface
module interface_user(
    simple_if.master m_if,
    input  logic     en,
    output logic     q
);
    assign q        = en & m_if.clk;
    assign m_if.data = q;
endmodule
module assertions(
    input  logic clk,
    input  logic req,
    input  logic ack,
    output logic good
);
    property handshake;
        @(posedge clk) req |-> ##1 ack;
    endproperty
    assert property (handshake);
    assume property (handshake);
    always_ff @(posedge clk)
        good <= req & ack;
endmodule
