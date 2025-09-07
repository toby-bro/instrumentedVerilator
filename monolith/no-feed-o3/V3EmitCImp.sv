`timescale 1ns/1ps
module param_mod #(parameter WIDTH = 8)
(
    input  logic [WIDTH-1:0] in_data,
    output logic [WIDTH-1:0] out_data
);
    function automatic logic [WIDTH-1:0] accumulate(input logic [WIDTH-1:0] x);
        static logic [WIDTH-1:0] sum = '0;
        sum = sum + x;
        return sum;
    endfunction
    assign out_data = accumulate(in_data);
endmodule
module coverage_enum_mod
(
    input  logic clk,
    input  logic rst_n,
    input  logic din,
    output logic dout
);
    typedef enum logic [1:0] { S_IDLE = 0, S_ACTIVE = 1, S_DONE = 2 } state_e;
    state_e state;
    covergroup cg_state @(posedge clk);
        coverpoint state;
    endgroup
    cg_state cg_inst = new;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= S_IDLE;
            dout  <= 1'b0;
        end else begin
            case (state)
                S_IDLE:   if (din) state <= S_ACTIVE;
                S_ACTIVE:        state <= S_DONE;
                S_DONE:          state <= S_IDLE;
                default:         state <= S_IDLE;
            endcase
            dout <= (state == S_DONE);
        end
    end
endmodule
module struct_array_mod
(
    input  logic        clk,
    input  logic [15:0] in_val,
    output logic [7:0]  out_val
);
    typedef struct {
        logic [7:0] a;
        logic [7:0] b;
    } pkt_t;
    pkt_t mem [0:3];
    always_ff @(posedge clk) begin
        mem[0].a <= in_val[15:8];
        mem[0].b <= in_val[7:0];
    end
    assign out_val = mem[0].b;
endmodule
module event_mod
(
    input  logic clk,
    output logic flag
);
    event ev;
    always_ff @(posedge clk) begin
        -> ev;
    end
    always @(ev) begin
        flag <= 1'b1;
    end
endmodule
module wide_array_mod
(
    input  logic        clk,
    input  logic [255:0] in_bus,
    output logic [255:0] out_bus
);
    logic [255:0] buf [0:3];
    always_ff @(posedge clk) begin
        buf[0]  <= in_bus;
        out_bus <= buf[0];
    end
endmodule
module class_proc_mod
(
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
    class helper_c;
        function int increment(int x);
            return x + 1;
        endfunction
    endclass
    always_comb begin
        helper_c obj = new();
        out_data = obj.increment(in_data);
    end
endmodule
