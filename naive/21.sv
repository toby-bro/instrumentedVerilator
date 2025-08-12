module arithmetic_unit #(
    parameter int WIDTH = 32
)(
    input  logic [WIDTH-1:0] in_a,
    input  logic [WIDTH-1:0] in_b,
    output logic [WIDTH-1:0] out_y
);
    function automatic logic [WIDTH-1:0] compute (
        input logic [WIDTH-1:0] a,
        input logic [WIDTH-1:0] b
    );
        compute = (a & b) | (a ^ b);
    endfunction
    always_comb begin
        out_y = compute(in_a, in_b);
    end
endmodule
module fsm_counter (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        start,
    output logic        done,
    output logic [3:0]  state_o
);
    typedef enum logic [1:0] {
        IDLE = 2'd0,
        RUN  = 2'd1,
        STOP = 2'd2
    } state_t;
    state_t state, next_state;
    logic [3:0] count;
    always_comb begin
        next_state = state;
        done       = 1'b0;
        case (state)
            IDLE: if (start) next_state = RUN;
            RUN:  if (count == 4'd9) next_state = STOP;
            STOP: begin
                done = 1'b1;
                if (!start) next_state = IDLE;
            end
            default: next_state = IDLE;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state  <= IDLE;
            count  <= 4'd0;
        end else begin
            state <= next_state;
            if (state == RUN)
                count <= count + 1'b1;
            else
                count <= 4'd0;
        end
    end
    assign state_o = {2'b00, state};
endmodule
module struct_union_demo (
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
    typedef struct packed {
        logic [3:0] hi;
        logic [3:0] lo;
    } nib_t;
    typedef union packed {
        nib_t        s;
        logic [7:0]  as_byte;
    } u_t;
    always_comb begin
        u_t u;
        u.as_byte = in_data;
        out_data  = {u.s.lo, u.s.hi};
    end
endmodule
module generate_parity #(
    parameter int LINES = 4
)(
    input  logic [LINES*8-1:0] in_bus,
    output logic [LINES-1:0]   parity
);
    genvar i;
    generate
        for (i = 0; i < LINES; i++) begin : parity_gen
            always_comb begin
                parity[i] = ^in_bus[i*8 +: 8];
            end
        end
    endgenerate
endmodule
module class_in_proc #(
    parameter int WIDTH = 16
)(
    input  logic [WIDTH-1:0] in_x,
    output logic [WIDTH-1:0] out_y
);
    class Multiplier;
        function automatic int mult(int a, int b);
            mult = a * b;
        endfunction
    endclass
    always_comb begin
        automatic Multiplier m = new();
        int r;
        r     = m.mult(in_x, 2);
        out_y = r[WIDTH-1:0];
    end
endmodule
module property_checker (
    input  logic       clk,
    input  logic [7:0] data_in,
    output logic       safe
);
    logic violation = 1'b0;
    property stable_data;
        @(posedge clk) data_in == $past(data_in);
    endproperty
    assert property (stable_data) else violation = 1'b1;
    always_comb begin
        safe = ~violation;
    end
endmodule
