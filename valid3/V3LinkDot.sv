package ptypes;
    typedef enum logic [1:0] {IDLE, BUSY, DONE} state_e;
endpackage
package util_pkg;
    import ptypes::*;
    class base_c;
        virtual function void foo(); endfunction
    endclass
    class derived_c extends base_c;
        rand int value;
        constraint c_val { value inside {[0:15]}; }
        function new(int v = 0);
            value = v;
        endfunction
        function void foo();
            value = value + 1;
        endfunction
    endclass
endpackage
interface bus_if #(parameter int W = 8) (input logic clk);
    logic [W-1:0] data;
    modport m (input clk, inout data);
endinterface
module leaf #(parameter int WIDTH = 8) (
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] inner
);
    typedef struct packed { logic [WIDTH-1:0] s; } data_s;
    data_s d;
    assign d.s   = in;
    assign inner = d.s;
endmodule
module hierarchy_mod (
    input  logic       clk,
    input  logic [7:0] a,
    output logic [7:0] b
);
    logic [7:0] leaf_inner;
    leaf #(.WIDTH(8)) leaf_inst (.in(a), .inner(leaf_inner));
    assign b = leaf_inner;
endmodule
module ifc_master (
    input  logic clk,
    output logic [7:0] q
);
    bus_if #(8) intf (clk);
    logic [7:0] q_reg;
    assign q         = q_reg;
    assign intf.data = q_reg;
endmodule
module genblk_mod #(
    parameter int N = 4
) (
    input  logic [N-1:0] in,
    output logic [N-1:0] out
);
    generate
        for (genvar i = 0; i < N; i++) begin : genblk
            assign out[i] = in[i];
        end
    endgenerate
endmodule
module clkblock (
    input  logic clk,
    input  logic d,
    output logic q
);
    clocking cb @(posedge clk);
        input  d;
        output q;
    endclocking
    always_comb q = cb.d;
endmodule
module param_type_mod #(
    parameter type T = int
) (
    input  T a,
    output T b
);
    T v;
    assign v = a;
    assign b = v;
endmodule
module class_param_mod #(
    parameter type C = util_pkg::derived_c
) (
    input  logic clk,
    output logic [31:0] out
);
    C obj = new();
    always_comb out = obj.value;
endmodule
module foreach_mod (
    input  logic [7:0] in  [0:3],
    output logic [7:0] out [0:3]
);
    always_comb begin
        foreach (in[i]) begin
            out[i] = in[i];
        end
    end
endmodule
