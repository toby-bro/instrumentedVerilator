import "DPI-C" function int dpi_add(input int a, input int b);
interface simple_if;
    logic data;
endinterface
typedef struct packed {
    logic [3:0] nibble;
    bit         flag;
} my_packed_t;
typedef enum logic [1:0] {RED = 2'd0, GREEN = 2'd1, BLUE = 2'd2} color_t;
module arithmetic_ops
(
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic [31:0] y_and,
    output logic [31:0] y_or,
    output logic [31:0] y_add,
    output logic        y_cmp
);
    assign y_and = a & b;
    assign y_or  = a | b;
    assign y_add = a + b;
    assign y_cmp = (a == b);
endmodule
module struct_packed_demo
(
    input  my_packed_t in_s,
    output logic [3:0] nibble_o,
    output bit         flag_o
);
    assign nibble_o = in_s.nibble;
    assign flag_o   = in_s.flag;
endmodule
module array_slice_demo
(
    input  logic [31:0] vector_in,
    output logic [7:0]  high_byte,
    output logic        bit7
);
    assign high_byte = vector_in[15:8];
    assign bit7      = vector_in[7];
endmodule
module queue_size_demo
(
    input  logic clk,
    input  int   in_val,
    output int   q_size_o
);
    int q[$];
    int qsize_reg;
    always_ff @(posedge clk) begin
        q.push_back(in_val);
        if (q.size() > 16) begin
            void'(q.pop_front());
        end
        qsize_reg <= q.size();
        q_size_o  <= qsize_reg;
    end
endmodule
class MyClass;
    int data;
    function new(int val = 0);
        data = val;
    endfunction
    function int get();
        return data;
    endfunction
    function void set(int v);
        data = v;
    endfunction
endclass
module class_handle_demo
(
    input  logic clk,
    input  int   in_data,
    output int   out_data
);
    MyClass obj;
    always_ff @(posedge clk) begin
        if (obj == null) begin
            obj = new(in_data);
        end else begin
            obj.set(in_data);
        end
        out_data <= obj.get();
    end
endmodule
module enum_demo
(
    input  color_t color_in,
    output logic   is_green_o
);
    assign is_green_o = (color_in == GREEN);
endmodule
module interface_user_demo
(
    input  logic unused_in,
    input  logic if_data_in,
    output logic data_out
);
    assign data_out = if_data_in ^ unused_in;
endmodule
module dpi_demo
(
    input  int a,
    input  int b,
    output int c
);
    always_comb begin
        c = dpi_add(a, b);
    end
endmodule
module event_demo
(
    input  logic trigger_in,
    output logic trigger_out
);
    event ev;
    always_ff @(posedge trigger_in) begin
        -> ev;
    end
    assign trigger_out = trigger_in;
endmodule
