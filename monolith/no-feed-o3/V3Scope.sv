package my_pkg;
    parameter int P = 4;
    int pkg_var = 0;
    function int add (input int a, input int b);
        add = a + b + P;
    endfunction
    task automatic set_pkg (input int v);
        pkg_var = v;
    endtask
    class my_class;
        int value;
        function new (input int v);
            value = v;
        endfunction
        function int get ();
            return value;
        endfunction
    endclass
endpackage
import "DPI-C" function int dpi_add (input int a, input int b);
interface bus_if (input logic clk);
    logic req;
    logic grant;
    modport master (output req, input grant);
    modport slave  (input req, output grant);
    always_ff @(posedge clk) begin
        grant <= req;
    end
endinterface
module child_mod (
    input  logic clk,
    input  logic in,
    output logic out
);
    import my_pkg::*;
    always_ff @(posedge clk) begin
        out <= in;
        set_pkg(out);
    end
    logic [31:0] sum;
    always_ff @(posedge clk) begin
        sum <= dpi_add(32'(out), 32'(in));
    end
    property p_level;
        @(posedge clk) in |-> out;
    endproperty
    cover property (p_level);
endmodule
module parent_mod (
    input  logic        clk,
    input  logic [7:0]  d_in,
    output logic        d_out
);
    import my_pkg::*;
    bus_if bus(clk);
    logic req_sig;
    alias bus.req = req_sig;
    assign req_sig = d_in[0];
    child_mod u_child (
        .clk (clk),
        .in  (bus.req),
        .out (bus.grant)
    );
    always_comb begin
        u_child.out = d_in[1];
    end
    assign d_out = bus.grant;
endmodule
module class_user_mod (
    input  logic        clk,
    input  logic [3:0]  a,
    output logic [3:0]  y
);
    import my_pkg::*;
    my_class c;
    always_ff @(posedge clk) begin
        c = new(a);
        y <= c.get();
    end
    covergroup cg1 @(posedge clk);
        coverpoint a;
    endgroup
    cg1 cg1_inst = new();
endmodule
module slave_mod (
    input  logic clk,
    input  logic req_in,
    output logic grant_out
);
    bus_if busS(clk);
    alias busS.req = req_in;
    always_ff @(posedge clk) begin
        busS.grant <= req_in;
    end
    assign grant_out = busS.grant;
endmodule
