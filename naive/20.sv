module param_adder #(parameter int WIDTH = 8) (
    input  logic [WIDTH-1:0] in_a,
    input  logic [WIDTH-1:0] in_b,
    output logic [WIDTH:0]   out_sum
);
    always_comb begin
        out_sum = in_a + in_b;
        assert (out_sum == in_a + in_b);
    end
endmodule
module fsm_example (
    input  logic clk,
    input  logic rst_n,
    input  logic in_event,
    output logic [1:0] out_state
);
    typedef enum logic [1:0] {
        IDLE  = 2'd0,
        ST_A  = 2'd1,
        ST_B  = 2'd2,
        ST_C  = 2'd3
    } state_e;
    state_e current_state, next_state;
    always_comb begin
        next_state = current_state;
        unique case (current_state)
            IDLE: if (in_event) next_state = ST_A;
            ST_A: next_state = ST_B;
            ST_B: next_state = ST_C;
            ST_C: next_state = IDLE;
            default: next_state = IDLE;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            current_state <= IDLE;
        else
            current_state <= next_state;
    end
    assign out_state = current_state;
endmodule
module struct_union (
    input  logic [31:0] in_data,
    output logic [15:0] out_low,
    output logic [15:0] out_high
);
    typedef struct packed {
        logic [15:0] low;
        logic [15:0] high;
    } word_s;
    typedef union packed {
        word_s       words;
        logic [31:0] full;
    } word_u;
    word_u u;
    always_comb begin
        u.full   = in_data;
        out_low  = u.words.low;
        out_high = u.words.high;
    end
endmodule
module generate_block #(
    parameter int N     = 4,
    parameter int WIDTH = 8
) (
    input  logic [N*WIDTH-1:0] bus_in,
    output logic [WIDTH-1:0]   bus_or
);
    logic [WIDTH-1:0] elements [N];
    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin : EXTRACT
            assign elements[i] = bus_in[i*WIDTH +: WIDTH];
        end
    endgenerate
    integer j;
    always_comb begin
        bus_or = '0;
        for (j = 0; j < N; j = j + 1) begin
            bus_or |= elements[j];
        end
    end
endmodule
module class_usage (
    input  logic        in_valid,
    input  logic [7:0]  in_a,
    input  logic [7:0]  in_b,
    output logic [8:0]  out_c
);
    class adder_c;
        function automatic int unsigned add (int unsigned a, int unsigned b);
            return a + b;
        endfunction
    endclass
    adder_c c_inst;
    always_ff @(posedge in_valid) begin
        c_inst = new();
        out_c  <= c_inst.add(in_a, in_b);
    end
endmodule
