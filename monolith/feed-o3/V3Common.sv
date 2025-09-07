interface data_if (input logic clk);
    logic req;
    logic ack;
    modport master (output req, input ack);
    modport slave  (input req, output ack);
endinterface
typedef struct packed {
    bit signed [31:0] m;
    bit        [7:0]  n;
} my_s;
typedef struct packed {
    bit [255:0] big_data;
    bit [31:0]  small;
} my_big_t;
typedef union packed {
    bit        [31:0] u32;
    bit signed [31:0] s;
} my_u;
class base_c;
    int b;
    function new (int v = 0);
        b = v;
    endfunction
    function int get ();
        return b;
    endfunction
endclass
class child_c extends base_c;
    bit [15:0]  y;
    bit [200:0] wide;
    my_big_t    big;
    function new (int v = 0, bit [15:0] w = 0);
        super.new(v);
        y         = w;
        wide      = '0;
        big.big_data = '0;
        big.small    = 32'h0;
    endfunction
    function void set_big (my_big_t val);
        big = val;
    endfunction
endclass
module class_demo_mod #(
    parameter int WIDTH = 4
) (
    input  logic [WIDTH-1:0] in1,
    output logic [WIDTH-1:0] out1
);
    child_c c;
    always_comb begin
        if (c == null) begin
            my_big_t tmp;
            tmp.big_data = '0;
            tmp.small    = 32'h0;
            c            = new (in1, {in1, in1, in1, in1});
            c.set_big(tmp);
        end
        out1 = in1;
    end
endmodule
module struct_demo_mod (
    input  logic       clk,
    input  logic [7:0] din,
    output logic [7:0] dout
);
    my_s s_var;
    always_ff @(posedge clk) begin
        s_var.n <= din;
        s_var.m <= $signed(din);
    end
    always_comb begin
        dout = s_var.n;
    end
endmodule
module union_demo_mod (
    input  logic        sel,
    input  logic [31:0] din,
    output logic signed [31:0] dout
);
    my_u u_var;
    always_comb begin
        if (sel) begin
            u_var.u32 = din;
        end else begin
            u_var.s   = $signed(din);
        end
        dout = $signed(u_var.s);
    end
endmodule
module wide_demo_mod (
    input  logic [255:0] in_w,
    output logic [255:0] out_w
);
    always_comb begin
        out_w = in_w;
    end
endmodule
