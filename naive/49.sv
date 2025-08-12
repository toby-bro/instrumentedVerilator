module bitwise_ops(
    input  logic [7:0] in_a,
    input  logic [7:0] in_b,
    output logic [7:0] out_y
);
    assign out_y = (in_a & in_b) | (~in_a & ~in_b);
endmodule
module enum_fsm #(
    parameter int WIDTH = 8
)(
    input  logic clk,
    input  logic rst_n,
    input  logic start,
    output logic done
);
    typedef enum logic [1:0] {
        IDLE,
        BUSY,
        DONE
    } state_t;
    state_t state, next_state;
    always_comb begin
        next_state = state;
        case (state)
            IDLE : if (start) next_state = BUSY;
            BUSY :           next_state = DONE;
            DONE :           next_state = IDLE;
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
module struct_union_demo(
    input  logic [15:0] in_data,
    output logic [7:0]  out_low,
    output logic [7:0]  out_high
);
    typedef struct packed {
        logic [7:0] low;
        logic [7:0] high;
    } word_t;
    word_t w;
    always_comb begin
        w = word_t'(in_data);
        out_low  = w.low;
        out_high = w.high;
    end
endmodule
module class_comb(
    input  logic [31:0] in_value,
    output logic [31:0] out_value
);
    class reverser;
        function automatic logic [31:0] reverse_bits(logic [31:0] val);
            logic [31:0] tmp;
            for (int i = 0; i < 32; i++) begin
                tmp[i] = val[31 - i];
            end
            return tmp;
        endfunction
    endclass
    always_comb begin
        reverser r = new();
        out_value = r.reverse_bits(in_value);
    end
endmodule
module generate_loop_demo #(
    parameter int BUS_WIDTH = 4
)(
    input  logic [BUS_WIDTH-1:0] bus_in,
    output logic [BUS_WIDTH-1:0] bus_out
);
    genvar i;
    generate
        for (i = 0; i < BUS_WIDTH; i++) begin : gen_blk
            assign bus_out[i] = ~bus_in[BUS_WIDTH-1-i];
        end
    endgenerate
endmodule
