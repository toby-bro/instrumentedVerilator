module param_mod #(
    parameter int WIDTH = 8,
    parameter int DEPTH = 16
) (
    input  logic                   clk,
    input  logic                   rst_n,
    output logic [WIDTH-1:0]       out
);
    localparam int MID = DEPTH / 2;
    assign out = MID[WIDTH-1:0];
endmodule
module gen_mod (
    input  logic [3:0] sel,
    input  logic       en,
    output logic       out
);
    logic [3:0] flag;
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : loop
            if (i == 0) begin
                assign flag[i] = sel[i] & en;
            end else begin
                assign flag[i] = sel[i] | en;
            end
        end
    endgenerate
    assign out = |flag;
endmodule
module always_ff_mod (
    input  logic clk,
    input  logic reset_n,
    input  logic d,
    output logic q
);
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            q <= 1'b0;
        else
            q <= d;
    end
endmodule
module always_comb_mod (
    input  logic [1:0] a,
    input  logic [1:0] b,
    output logic [1:0] y
);
    always_comb begin
        case (a)
            2'd0: y = b;
            2'd1: y = a;
            default: y = a ^ b;
        endcase
    end
endmodule
module always_latch_mod (
    input  logic en,
    input  logic d,
    output logic q
);
    always_latch begin
        if (en)
            q = d;
    end
endmodule
module func_task_mod (
    input  logic [7:0] a,
    input  logic [7:0] b,
    input  logic       calltsk,
    output logic [7:0] sum,
    output logic       eq
);
    function logic [7:0] add(input logic [7:0] x, input logic [7:0] y);
        add = x + y;
    endfunction
    task check(input  logic [7:0] x, input logic [7:0] y, output logic result);
        result = (x == y);
    endtask
    always_comb begin
        sum = add(a, b);
        if (calltsk)
            check(a, b, eq);
        else
            eq = 1'b0;
    end
endmodule
module struct_union_mod (
    input  logic [1:0] sel,
    input  logic [7:0] vin,
    output logic [7:0] vout
);
    typedef struct packed {
        logic [3:0] hi;
        logic [3:0] lo;
    } half_t;
    typedef union packed {
        half_t        h;
        logic [7:0]  all;
    } u_t;
    u_t data;
    always_comb begin
        data.all = vin;
        case (sel)
            2'd0: vout = {4'b0, data.h.hi};
            2'd1: vout = {4'b0, data.h.lo};
            default: vout = data.all;
        endcase
    end
endmodule
module enum_mod (
    input  logic       clk,
    input  logic       reset,
    input  logic       go,
    output logic [1:0] state
);
    typedef enum logic [1:0] {
        IDLE = 2'd0,
        BUSY = 2'd1,
        DONE = 2'd2
    } st_t;
    st_t current, next;
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            current <= IDLE;
        else
            current <= next;
    end
    always_comb begin
        case (current)
            IDLE: next = go ? BUSY : IDLE;
            BUSY: next = DONE;
            DONE: next = IDLE;
            default: next = IDLE;
        endcase
        state = current;
    end
endmodule
module pack_array_mod (
    input  logic [7:0] din [0:3],
    input  logic [1:0] idx,
    output logic [7:0] dout
);
    logic [7:0] arr [0:3];
    assign arr = din;
    assign dout = arr[idx];
endmodule
module specify_mod (
    input  wire a,
    input  wire b,
    output wire y
);
    assign y = a & b;
    specify
        (a => y) = 1;
        (b => y) = 1;
    endspecify
endmodule
