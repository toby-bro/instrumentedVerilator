interface simple_if;
    logic a;
endinterface
interface bus_if;
    logic data;
endinterface
class util_c;
    int id_value;
    function new();
        id_value = 42;
    endfunction
    function int id();
        return id_value;
    endfunction
endclass
(* inline_module *)
module child_inline1 #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] in1,
    output logic [WIDTH-1:0] out1
);
    always_comb begin
        automatic util_c c;
        automatic int dummy;
        c = new();
        dummy = c.id();
        out1 = ~in1;
    end
endmodule
module parent_inline (
    input  logic [7:0] a,
    output logic [7:0] y
);
    logic [7:0] stage0;
    logic [7:0] stage1;
    child_inline1 #(.WIDTH(8)) u0 (.in1(a),      .out1(stage0));
    child_inline1 #(.WIDTH(8)) u1 (.in1(stage0), .out1(stage1));
    assign y = stage1;
endmodule
(* no_inline_module *)
module child_no_inline (
    input  logic signed [3:0] inx,
    output logic signed [3:0] outx
);
    typedef struct packed {logic signed [3:0] val;} my_t;
    my_t s;
    always_comb begin
        automatic util_c c2;
        automatic int dummy2;
        c2 = new();
        dummy2 = c2.id();
        s.val = inx + 1;
        outx  = s.val;
    end
endmodule
module parent_no_inline (
    input  logic signed [3:0] in_val,
    output logic signed [3:0] out_val
);
    child_no_inline ni0 (.inx(in_val), .outx(out_val));
endmodule
(* inline_module *)
module if_child (
    bus_if iface,
    input  logic din,
    output logic dout
);
    assign iface.data = din;
    assign dout       = iface.data;
endmodule
module interface_parent (
    bus_if iface,
    input  logic din,
    output logic dout
);
    if_child ic0 (.iface(iface), .din(din), .dout(dout));
endmodule
module wrapper_if (
    input  logic din,
    output logic dout
);
    bus_if iface();
    interface_parent ip0 (.iface(iface), .din(din), .dout(dout));
endmodule
module pub_array_mod (
    input  logic [3:0] idx,
    input  logic [3:0] val,
    output logic [3:0] first_elem
);
    logic [3:0] reg_array [0:3];
    always_comb begin
        automatic util_c c3;
        automatic int dummy3;
        c3 = new();
        dummy3 = c3.id();
        reg_array[idx[1:0]] = val;
        first_elem = reg_array[0];
    end
endmodule
