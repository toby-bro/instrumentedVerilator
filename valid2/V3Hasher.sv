package my_pkg;
    function automatic int add(input int a, b);
        add = a + b;
    endfunction
endpackage
interface my_if;
    logic data;
    modport m (input data);
endinterface
import "DPI-C" function int cfunc(input int a);
module child_unit (
    input  logic in_c,
    output logic out_c
);
    assign out_c = ~in_c;
endmodule
module parent_unit (
    input  logic in_p,
    output logic out_p
);
    wire w;
    child_unit u_child (.in_c(in_p), .out_c(w));
    assign out_p = w;
endmodule
module array_features #(
    parameter WIDTH = 8
) (
    input  logic [WIDTH-1:0] in_val,
    output logic [WIDTH-1:0] out_val
);
    int static_array [0:3];
    int dynamic_array [];
    int queue_array   [$];
    int associative_array [int];
    int unsized_array [];
    always_comb begin
        static_array[0] = in_val;
        out_val         = static_array[0];
    end
endmodule
module struct_enum_union (
    input  logic [3:0] ctrl,
    output logic [7:0] result
);
    typedef enum logic [2:0] {IDLE, S1, S2} state_e;
    typedef struct packed {
        logic [7:0] a;
        logic [7:0] b;
    } packed_s;
    typedef union packed {
        logic [15:0] word;
        packed_s     bytes;
    } packed_u;
    state_e  state;
    packed_u data_u;
    always_comb begin
        data_u.word = 16'hA5A5;
        case (ctrl[1:0])
            2'd0: result = data_u.bytes.a;
            2'd1: result = data_u.bytes.b;
            default: result = 8'h00;
        endcase
    end
endmodule
module class_usage (
    input  logic       clk,
    input  logic [7:0] din,
    output logic [7:0] dout
);
    class my_class;
        logic [7:0] data;
        function new; data = 0; endfunction
        function void set(input logic [7:0] d); data = d; endfunction
    endclass
    my_class obj;
    always_ff @(posedge clk) begin
        if (obj == null) obj = new();
        obj.set(din);
        dout <= obj.data;
    end
endmodule
module cast_sel_demo (
    input  logic [31:0] in_data,
    output logic [15:0] out_low
);
    logic [7:0] bytes [3:0];
    always_comb begin
        bytes[0] = in_data[7:0];
        bytes[1] = in_data[15:8];
        bytes[2] = in_data[23:16];
        bytes[3] = in_data[31:24];
        out_low  = 16'(in_data[15:0]);
    end
endmodule
module modport_user (
    input  logic dummy_in,
    output logic dummy_out
);
    my_if if_inst();
    assign if_inst.data = dummy_in;
    assign dummy_out    = dummy_in ^ if_inst.data;
endmodule
module param_type_mod #(
    parameter type T = int
) (
    input  T in_sig,
    output T out_sig
);
    assign out_sig = T'(in_sig);
endmodule
module dpi_caller (
    input  logic       clk,
    input  int         operand,
    output logic [31:0] result
);
    int dpi_val;
    always_ff @(posedge clk) begin
        dpi_val <= cfunc(operand);
        result  <= $unsigned(dpi_val);
    end
endmodule
