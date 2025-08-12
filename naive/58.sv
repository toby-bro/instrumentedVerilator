module simple_and(input logic a, input logic b, output logic y);
    assign y = a & b;
endmodule
module reg_store(input logic clk, input logic rst, input logic d, output logic q);
    always_ff @(posedge clk) begin
        if (rst) q <= 0;
        else q <= d;
    end
endmodule
module comb_case(input logic [1:0] sel,
                 input logic [7:0] data0,
                 input logic [7:0] data1,
                 input logic [7:0] data2,
                 input logic [7:0] data3,
                 output logic [7:0] out);
    always_comb begin
        case (sel)
            2'b00: out = data0;
            2'b01: out = data1;
            2'b10: out = data2;
            2'b11: out = data3;
            default: out = '0;
        endcase
    end
endmodule
module param_adder #(parameter WIDTH = 8)(
    input logic [WIDTH-1:0] in0,
    input logic [WIDTH-1:0] in1,
    output logic [WIDTH:0] sum
);
    assign sum = in0 + in1;
endmodule
module gen_shifter #(parameter WIDTH = 8)(
    input logic [WIDTH-1:0] in,
    input logic [2:0] shift,
    output logic [WIDTH-1:0] out
);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i = i + 1) begin : shift_loop
            assign out[i] = (i + shift < WIDTH) ? in[i + shift] : 1'b0;
        end
    endgenerate
endmodule
module fsm_example(input logic clk, input logic rst, input logic in, output logic out);
    typedef enum logic [1:0] {IDLE, STATE1, STATE2, STATE3} state_t;
    state_t state;
    always_ff @(posedge clk) begin
        if (rst) state <= IDLE;
        else begin
            case (state)
                IDLE:   if (in) state <= STATE1;
                STATE1: state <= STATE2;
                STATE2: state <= STATE3;
                STATE3: state <= IDLE;
                default: state <= IDLE;
            endcase
        end
    end
    assign out = (state == STATE3);
endmodule
module struct_example(input logic [3:0] a, input logic [3:0] b, output logic [4:0] result);
    typedef struct packed {
        logic signed [4:0] low;
        logic signed [4:0] high;
    } pair_t;
    pair_t p;
    always_comb begin
        p.low  = $signed(a);
        p.high = $signed(b);
        result = p.low + p.high;
    end
endmodule
module class_example(input logic clk, input logic rst, input logic in, output logic out);
    class simple_class;
        logic bit_in;
        function void compute(input logic in_signal);
            bit_in = in_signal;
        endfunction
    endclass
    simple_class inst_ptr;
    logic out_reg;
    always_ff @(posedge clk) begin
        if (rst) begin
            inst_ptr = new;
            out_reg  <= 0;
        end else begin
            inst_ptr.compute(in);
            out_reg <= inst_ptr.bit_in;
        end
    end
    assign out = out_reg;
endmodule
module function_example(input logic [7:0] a, input logic [7:0] b, output logic [7:0] y);
    function logic [7:0] my_func(input logic [7:0] x, input logic [7:0] y_in);
        my_func = x ^ y_in;
    endfunction
    assign y = my_func(a, b);
endmodule
module union_example(input logic [7:0] in, output logic [3:0] high, output logic [3:0] low);
    typedef union packed {
        logic [7:0] byte_field;
        struct packed {
            logic [3:0] lo;
            logic [3:0] hi;
        } parts;
    } u_t;
    u_t u;
    always_comb begin
        u.byte_field = in;
        high = u.parts.hi;
        low  = u.parts.lo;
    end
endmodule
