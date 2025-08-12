package common_pkg;
    typedef struct packed {
        logic [7:0] data;
        logic       parity;
    } pkt_t;
    typedef enum logic [1:0] {
        IDLE = 2'd0,
        BUSY = 2'd1,
        DONE = 2'd2
    } state_t;
endpackage
module arithmetic_unit #(
    parameter int WIDTH = 8
)(
    input  logic                   clk,
    input  logic [WIDTH-1:0]       a,
    input  logic [WIDTH-1:0]       b,
    output logic [WIDTH-1:0]       sum
);
    always_ff @(posedge clk) begin
        sum <= a + b;
    end
endmodule
module parity_checker(
    input  common_pkg::pkt_t       pkt_in,
    output logic                   parity_ok
);
    assign parity_ok = (^pkt_in.data) == pkt_in.parity;
endmodule
module state_machine(
    input  logic                   clk,
    input  logic                   rst_n,
    input  logic                   start,
    output logic                   done
);
    import common_pkg::*;
    state_t state, next;
    always_comb begin
        next = state;
        case (state)
            IDLE:  if (start) next = BUSY;
            BUSY:             next = DONE;
            DONE:             next = IDLE;
            default:          next = IDLE;
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
module class_processor(
    input  logic [15:0]            data_in,
    output logic [15:0]            data_out
);
    class manip;
        bit [15:0] d;
        function new(bit [15:0] v);
            d = v;
        endfunction
        function bit [15:0] transform();
            return ~d;
        endfunction
    endclass
    always_comb begin
        manip m = new(data_in);
        data_out = m.transform();
    end
endmodule
module generate_demo #(
    parameter bit USE_AND = 1'b1
)(
    input  logic                   a,
    input  logic                   b,
    output logic                   y
);
    generate
        if (USE_AND) begin : and_blk
            assign y = a & b;
        end else begin : or_blk
            assign y = a | b;
        end
    endgenerate
endmodule
module union_demo(
    input  logic [31:0]            word_in,
    output logic [7:0]             byte0_out
);
    union packed {
        logic [31:0]        w;
        logic [3:0][7:0]    b;
    } u;
    always_comb begin
        u.w       = word_in;
        byte0_out = u.b[0];
    end
endmodule
module assertion_demo(
    input  logic                   clk,
    input  logic                   en,
    input  logic                   data,
    output logic                   safe
);
    assign safe = en & data;
    property p_en_data;
        @(posedge clk) disable iff (!en) data |-> ##1 safe;
    endproperty
    assert property (p_en_data);
endmodule
