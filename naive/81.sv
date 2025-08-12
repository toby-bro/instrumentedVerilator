module mod_params #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    assign out = in;
endmodule
module mod_alu (
    input  logic a,
    input  logic b,
    output logic sum,
    output logic carry
);
    always_comb begin
        {carry, sum} = a + b;
    end
endmodule
module mod_regfile (
    input  logic          clk,
    input  logic          rst,
    input  logic [7:0]    d,
    output logic [7:0]    q
);
    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            q <= '0;
        else
            q <= d;
    end
endmodule
module mod_mult2 (
    input  logic signed [3:0] a,
    input  logic signed [3:0] b,
    output logic signed [7:0] out
);
    assign out = a * b;
endmodule
module mod_queue #(
    parameter DEPTH = 4
) (
    input  logic          clk,
    input  logic          enq,
    input  logic          deq,
    input  logic [7:0]    data_in,
    output logic [7:0]    data_out,
    output logic          full,
    output logic          empty
);
    logic [7:0] mem [0:DEPTH-1];
    logic [$clog2(DEPTH):0] rd_ptr, wr_ptr;
    assign full  = (wr_ptr + 1 == rd_ptr);
    assign empty = (wr_ptr == rd_ptr);
    always_ff @(posedge clk) begin
        if (enq && !full) begin
            mem[wr_ptr] <= data_in;
            wr_ptr <= wr_ptr + 1;
        end
        if (deq && !empty) begin
            data_out <= mem[rd_ptr];
            rd_ptr <= rd_ptr + 1;
        end
    end
endmodule
module mod_struct (
    input  logic       clk,
    input  logic       enable,
    output logic [7:0] sum
);
    typedef struct packed {
        logic [3:0] a;
        logic [3:0] b;
    } sbus_t;
    sbus_t bus;
    always_ff @(posedge clk) begin
        if (enable)
            bus.a <= bus.a + 1;
    end
    assign sum = bus.a + bus.b;
endmodule
module mod_class_inst (
    input  logic       clk,
    input  logic       rst,
    input  logic [7:0] in,
    output logic [7:0] out
);
    class myclass;
        rand logic [7:0] data;
        function void update(logic [7:0] val);
            data = val;
        endfunction
    endclass
    myclass obj;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            obj = new();
        end else begin
            obj.update(in);
        end
    end
    always_comb begin
        if (obj != null)
            out = obj.data;
        else
            out = '0;
    end
endmodule
module mod_fun (
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic [4:0] res
);
    function automatic logic [4:0] add(input logic [3:0] x, input logic [3:0] y);
        add = x + y;
    endfunction
    assign res = add(a, b);
endmodule
module mod_generate #(
    parameter N = 4
) (
    input  logic [N-1:0] in,
    output logic [N-1:0] out
);
    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin : gen_loop
            assign out[i] = in[i];
        end
    endgenerate
endmodule
