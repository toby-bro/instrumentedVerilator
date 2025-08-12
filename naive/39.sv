class calc_c;
    function automatic int add(input int a, b);
        add = a + b;
    endfunction
    function automatic int mul(input int a, b);
        mul = a * b;
    endfunction
endclass
typedef struct packed {
    logic [7:0] data;
    logic       valid;
} packet_t;
typedef enum logic [1:0] {IDLE, LOAD, PROCESS, DONE} state_e;
typedef struct packed {
    logic [15:0] lower;
    logic [15:0] upper;
} half_t;
typedef struct packed {
    logic [7:0] b0;
    logic [7:0] b1;
    logic [7:0] b2;
    logic [7:0] b3;
} byte_t;
typedef union packed {
    logic [31:0] word;
    half_t       half;
    byte_t       bytes;
} reg_u;
module param_adder #(
    parameter WIDTH = 16
) (
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic [WIDTH:0]   sum
);
    always_comb begin
        sum = a + b;
    end
endmodule
module processor (
    input  logic    clk,
    input  logic    rst_n,
    input  packet_t in_pkt,
    output logic    ready
);
    state_e state, next;
    always_comb begin
        next  = state;
        ready = 1'b0;
        case (state)
            IDLE:    if (in_pkt.valid)            next = LOAD;
            LOAD:    next = PROCESS;
            PROCESS: next = DONE;
            DONE:    begin next = IDLE; ready = 1'b1; end
            default: next = IDLE;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next;
    end
endmodule
module packer (
    input  logic        sel,
    input  logic [31:0] din,
    output logic [15:0] dout
);
    reg_u reg_data;
    always_comb begin
        reg_data.word = din;
        dout          = sel ? reg_data.half.upper : reg_data.half.lower;
    end
endmodule
module wide_or #(
    parameter WIDTH = 64
) (
    input  logic [WIDTH-1:0] in_bus,
    output logic             or_out
);
    genvar i;
    wire [WIDTH-1:0] temp;
    generate
        for (i = 0; i < WIDTH; i++) begin : gen_or
            assign temp[i] = in_bus[i];
        end
    endgenerate
    assign or_out = |temp;
endmodule
module class_compute #(
    parameter WIDTH = 8
) (
    input  logic signed [WIDTH-1:0]      i1,
    input  logic signed [WIDTH-1:0]      i2,
    input  logic                         mode,
    output logic signed [(2*WIDTH)-1:0]  result
);
    always_comb begin
        automatic calc_c c = new();
        if (mode)
            result = c.mul(i1, i2);
        else
            result = c.add(i1, i2);
    end
endmodule
module array_stat (
    input  logic       clk,
    input  logic       rst_n,
    input  logic [7:0] din,
    output logic [7:0] max_val
);
    logic [7:0] data_q[$];
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_q.delete();
            max_val <= 0;
        end else begin
            data_q.push_back(din);
            if (din > max_val)
                max_val <= din;
        end
    end
endmodule
