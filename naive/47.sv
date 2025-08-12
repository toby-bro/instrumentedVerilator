interface bus_if #(parameter WIDTH = 8) (input logic clk);
    logic [WIDTH-1:0] data;
    logic             valid;
    modport master (output data, output valid, input clk);
    modport slave  (input  data, input  valid, input clk);
endinterface
module arithmetic_unit #(parameter WIDTH = 8)(
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    input  logic             add_sub,
    output logic [WIDTH-1:0] y
);
    always_comb begin
        if (add_sub)
            y = a + b;
        else
            y = a - b;
    end
endmodule
module enum_state_machine(
    input  logic clk,
    input  logic rst_n,
    input  logic start,
    output logic done
);
    typedef enum logic [1:0] {IDLE, BUSY, FINISH} state_t;
    state_t state, next;
    always_comb begin
        next = state;
        done = 1'b0;
        case (state)
            IDLE:   if (start) next = BUSY;
            BUSY:   next = FINISH;
            FINISH: begin
                        done = 1'b1;
                        next = IDLE;
                    end
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next;
    end
endmodule
module struct_union_example(
    input  logic [31:0] data_in,
    input  logic        sel,
    output logic [7:0]  data_out
);
    typedef struct packed {
        logic [7:0] byte0;
        logic [7:0] byte1;
        logic [7:0] byte2;
        logic [7:0] byte3;
    } bytes_t;
    union packed {
        logic  [31:0] word;
        bytes_t       bytes;
    } u_data;
    always_comb begin
        u_data.word = data_in;
        data_out    = sel ? u_data.bytes.byte2 : u_data.bytes.byte0;
    end
endmodule
module interface_slave #(parameter WIDTH = 8)(
    input  logic             clk,
    input  logic [WIDTH-1:0] data,
    input  logic             valid,
    output logic             ready
);
    always_ff @(posedge clk) begin
        ready <= valid;
    end
endmodule
module gen_example #(parameter WIDTH = 4, parameter USE_XOR = 0)(
    input  logic [WIDTH-1:0] din,
    output logic             parity
);
    generate
        if (USE_XOR) begin : g_xor
            always_comb parity = ^din;
        end else begin : g_and
            always_comb parity = &din;
        end
    endgenerate
endmodule
module assertion_module(
    input  logic clk,
    input  logic signal_in,
    output logic pass_through
);
    always_comb pass_through = signal_in;
    property sig_stable;
        @(posedge clk) signal_in |-> ##1 signal_in;
    endproperty
    assert property (sig_stable);
endmodule
module class_example(
    input  logic       clk,
    input  logic [7:0] value_in,
    output logic [7:0] value_out
);
    class mult2;
        function logic [7:0] fn (input logic [7:0] x);
            fn = x << 1;
        endfunction
    endclass
    mult2 m;
    always_ff @(posedge clk) begin
        m = new();
        value_out <= m.fn(value_in);
    end
endmodule
