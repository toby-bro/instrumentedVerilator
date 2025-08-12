module comb_and (
    input  logic a,
    input  logic b,
    output logic y
);
    assign y = a & b;
endmodule
module param_counter #(
    parameter WIDTH = 8
) (
    input  logic                   clk,
    input  logic                   rst_n,
    input  logic [WIDTH-1:0]       inc,
    output logic [WIDTH-1:0]       cnt
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            cnt <= '0;
        else
            cnt <= cnt + inc;
    end
endmodule
module simple_fsm (
    input  logic clk,
    input  logic rst_n,
    input  logic trigger,
    output logic active
);
    typedef enum logic [1:0] { IDLE = 2'b00, RUN = 2'b01, DONE = 2'b10 } state_t;
    state_t state, next;
    always_comb begin
        next = state;
        case (state)
            IDLE : if (trigger) next = RUN;
            RUN  :             next = DONE;
            DONE : if (!trigger) next = IDLE;
            default : next = IDLE;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next;
    end
    assign active = (state == RUN);
endmodule
module struct_pack (
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic [7:0] c
);
    typedef struct packed {
        logic [3:0] low;
        logic [3:0] high;
    } two_nibble_t;
    two_nibble_t temp;
    always_comb begin
        temp.low  = a;
        temp.high = b;
        c         = {temp.high, temp.low};
    end
endmodule
module gen_mux #(
    parameter WIDTH = 4,
    parameter SELW  = $clog2(WIDTH)
) (
    input  logic [WIDTH-1:0] in,
    input  logic [SELW-1:0]  sel,
    output logic             y
);
    generate
        if (WIDTH == 1) begin : gen_single
            assign y = in[0];
        end else begin : gen_multi
            always_comb begin
                y = in[sel];
            end
        end
    endgenerate
endmodule
module class_inst (
    input  logic i,
    output logic o
);
    class dummy;
        function bit invert(bit x);
            return ~x;
        endfunction
    endclass
    dummy d;
    initial begin
        d = new();
    end
    always_comb begin
        if (d == null)
            o = 1'b0;
        else
            o = d.invert(i);
    end
endmodule
