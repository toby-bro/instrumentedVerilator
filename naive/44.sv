package utils_pkg;
    typedef enum logic [1:0] {ST_IDLE = 2'd0,
                              ST_RUN  = 2'd1,
                              ST_DONE = 2'd2,
                              ST_ERR  = 2'd3} state_e;
    typedef struct packed {
        logic [7:0] data;
        logic       valid;
        logic [6:0] pad;
    } payload_t;
    typedef union packed {
        logic [15:0] word;
        payload_t    parts;
    } word_union_t;
    class accumulator #(int W = 8);
        logic [W-1:0] sum;
        function new();            sum = '0;     endfunction
        function void add(input logic [W-1:0] v); sum = sum + v; endfunction
        function logic [W-1:0] get(); return sum; endfunction
    endclass
endpackage
module arithmetic_unit #(
    parameter int WIDTH = 8
) (
    input  logic                 clk,
    input  logic                 reset,
    input  logic [WIDTH-1:0]     in_a,
    input  logic [WIDTH-1:0]     in_b,
    input  logic                 op_add_sub,
    output logic [WIDTH-1:0]     result,
    output logic                 carry
);
    import utils_pkg::*;
    logic [WIDTH:0] tmp;
    accumulator #(WIDTH) acc_h;
    always_comb begin
        if (op_add_sub == 1'b0)
            tmp = in_a + in_b;
        else
            tmp = in_a - in_b;
        result = tmp[WIDTH-1:0];
        carry  = tmp[WIDTH];
    end
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            acc_h = null;
        end else begin
            if (acc_h == null) acc_h = new();
            acc_h.add(result);
        end
    end
    assert property (@(posedge clk) disable iff (reset) !$isunknown(result));
endmodule
module simple_fsm (
    input  logic clk,
    input  logic reset,
    input  logic start,
    output logic busy,
    output logic done
);
    import utils_pkg::*;
    state_e state;
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            state <= ST_IDLE;
        else begin
            unique case (state)
                ST_IDLE : if (start) state <= ST_RUN;
                ST_RUN  :           state <= ST_DONE;
                ST_DONE :           state <= ST_IDLE;
                default :           state <= ST_ERR;
            endcase
        end
    end
    assign busy = (state == ST_RUN);
    assign done = (state == ST_DONE);
    cover property (@(posedge clk) state == ST_DONE);
endmodule
module barrel_shifter (
    input  logic [31:0] din,
    input  logic [4:0]  shamt,
    input  logic        dir,
    output logic [31:0] dout
);
    genvar i;
    logic [31:0] left_shifted  [0:5];
    logic [31:0] right_shifted [0:5];
    assign left_shifted [0]  = din;
    assign right_shifted[0]  = din;
    generate
        for (i = 0; i < 5; i++) begin : gen_shift
            assign left_shifted [i+1]  = (shamt[i]) ? (left_shifted [i]  << (1<<i)) : left_shifted [i];
            assign right_shifted[i+1]  = (shamt[i]) ? (right_shifted[i] >> (1<<i)) : right_shifted[i];
        end
    endgenerate
    assign dout = dir ? right_shifted[5] : left_shifted[5];
endmodule
module pattern_checker (
    input  logic       clk,
    input  logic       reset,
    input  logic [7:0] data_in,
    output logic       match
);
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            match <= 1'b0;
        else
            match <= (data_in == 8'hA);
    end
    sequence seq_two_A;
        data_in == 8'hA ##1 data_in == 8'hA;
    endsequence
    property p_detect;
        @(posedge clk) disable iff (reset) seq_two_A;
    endproperty
    assert property (p_detect);
    cover  property (p_detect);
endmodule
module aggregator #(
    parameter int WIDTH = 16,
    parameter int DEPTH = 4
) (
    input  logic                   clk,
    input  logic                   reset,
    input  logic [WIDTH-1:0]       in_data,
    input  logic                   in_valid,
    output logic [WIDTH-1:0]       out_sum
);
    import utils_pkg::*;
    logic [WIDTH-1:0] data_mem [DEPTH];
    logic [$clog2(DEPTH)-1:0] wr_ptr;
    word_union_t              converter;
    accumulator #(WIDTH)      acc_h;
    int                       k;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            wr_ptr <= '0;
            acc_h  = null;
        end else begin
            if (in_valid) begin
                data_mem[wr_ptr] <= in_data;
                wr_ptr           <= wr_ptr + 1;
            end
            if (acc_h == null) acc_h = new();
            acc_h.sum = '0;
            for (k = 0; k < DEPTH; k++) begin
                acc_h.add(data_mem[k]);
            end
        end
    end
    always_comb begin
        converter.word = (acc_h == null) ? '0 : acc_h.get();
    end
    assign out_sum = converter.word;
endmodule
