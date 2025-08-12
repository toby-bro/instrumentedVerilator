module param_adder #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic [WIDTH:0]   sum
);
    always_comb begin
        sum = a + b;
    end
endmodule
module simple_fsm (
    input  logic clk,
    input  logic rst_n,
    input  logic in_sig,
    output logic [1:0] state_o
);
    typedef enum logic [1:0] {S0, S1, S2} state_t;
    state_t state, next_state;
    always_comb begin
        next_state = state;
        unique case (state)
            S0: if (in_sig) next_state = S1;
            S1:              next_state = S2;
            S2:              next_state = S0;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) state <= S0;
        else        state <= next_state;
    end
    assign state_o = state;
endmodule
module struct_pack #(parameter WIDTH = 4) (
    input  logic [WIDTH-1:0] in_bus,
    output logic [WIDTH-1:0] out_bus
);
    localparam HALF = WIDTH/2;
    typedef struct packed {
        logic [HALF-1:0] upper;
        logic [HALF-1:0] lower;
    } split_t;
    split_t s;
    always_comb begin
        s.upper = in_bus[WIDTH-1:HALF];
        s.lower = in_bus[HALF-1:0];
        out_bus = {s.lower, s.upper};
    end
endmodule
module union_example (
    input  logic [31:0] in_data,
    output logic [7:0]  out_byte0
);
    typedef union packed {
        logic [31:0]       word;
        logic [3:0][7:0]   bytes;
    } data_u;
    data_u u;
    always_comb begin
        u.word     = in_data;
        out_byte0  = u.bytes[0];
    end
endmodule
module generate_mask #(parameter WIDTH = 16) (
    input  logic [WIDTH-1:0] in_mask,
    output logic             parity
);
    logic parity_array [WIDTH-1:0];
    genvar i;
    generate
        for (i = 0; i < WIDTH; i = i + 1) begin : gen_parity
            assign parity_array[i] = in_mask[i];
        end
    endgenerate
    always_comb begin
        parity = ^in_mask;
    end
endmodule
module func_calc (
    input  logic [15:0] val_in,
    output logic [15:0] square_out
);
    function automatic [15:0] square(input [15:0] x);
        square = x * x;
    endfunction
    always_comb begin
        square_out = square(val_in);
    end
endmodule
