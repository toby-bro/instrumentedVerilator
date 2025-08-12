module combine_op #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic [WIDTH-1:0] y
);
    always_comb begin
        y = (a & b) ^ (a | b);
    end
endmodule
module state_reg #(parameter WIDTH = 8) (
    input  logic               clk,
    input  logic               rst_n,
    input  logic [WIDTH-1:0]   d,
    output logic [WIDTH-1:0]   q
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            q <= '0;
        else
            q <= d;
    end
endmodule
module struct_example (
    input  logic [7:0] in0,
    output logic [7:0] out0
);
    typedef struct packed {
        logic [3:0] nibble0;
        logic [3:0] nibble1;
    } nibbles_t;
    nibbles_t s;
    always_comb begin
        s    = nibbles_t'(in0);
        out0 = {s.nibble1, s.nibble0};
    end
endmodule
module enum_example (
    input  logic [1:0] sel,
    output logic       act
);
    typedef enum logic [1:0] {
        IDLE = 2'b00,
        RUN  = 2'b01,
        DONE = 2'b10
    } state_t;
    state_t state;
    always_comb begin
        state = state_t'(sel);
        act   = (state == RUN);
    end
endmodule
module class_example (
    input  logic [7:0] din,
    output logic [7:0] dout
);
    class multiplier;
        function automatic logic [7:0] mul_by2 (logic [7:0] val);
            return val << 1;
        endfunction
    endclass
    multiplier mul_handle;
    always_comb begin
        mul_handle = new();
        dout       = mul_handle.mul_by2(din);
    end
endmodule
module function_task_example (
    input  logic [7:0] a,
    output logic [7:0] y
);
    function automatic logic [7:0] reverse_bits (input logic [7:0] val);
        integer i;
        logic [7:0] tmp;
    begin
        tmp = '0;
        for (i = 0; i < 8; i++) begin
            tmp[i] = val[7 - i];
        end
        return tmp;
    end
    endfunction
    always_comb y = reverse_bits(a);
endmodule
module generate_example #(parameter WIDTH = 16) (
    input  logic [WIDTH-1:0] in_bus,
    output logic [WIDTH-1:0] out_bus
);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : gen_block
            always_comb begin
                out_bus[i] = in_bus[WIDTH - 1 - i];
            end
        end
    endgenerate
endmodule
module assert_example (
    input  logic clk,
    input  logic a,
    output logic pass
);
    property p_always_high;
        @(posedge clk) a |-> ##1 a;
    endproperty
    assert property (p_always_high);
    assign pass = a;
endmodule
module typedef_example (
    input  logic [31:0] data_in,
    output logic [15:0] upper
);
    typedef union packed {
        logic [31:0] word;
        struct packed {
            logic [7:0] byte0;
            logic [7:0] byte1;
            logic [7:0] byte2;
            logic [7:0] byte3;
        } bytes;
    } data_u;
    data_u u;
    always_comb begin
        u.word = data_in;
        upper  = {u.bytes.byte3, u.bytes.byte2};
    end
endmodule
