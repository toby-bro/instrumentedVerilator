package pkga;
    parameter int WIDTH = 8;
    typedef logic [WIDTH-1:0] word_t;
endpackage
package pkgb;
    import pkga::*;
    function int add (int x);
        add = x + WIDTH;
    endfunction
endpackage
interface bus_if (input logic clk);
    logic req, gnt;
    logic [7:0] data;
    modport master (input clk, output req, input gnt, output data);
    modport slave  (input clk, input req, output gnt, input data);
    modport exp (output .r(req), input .g(gnt), input .d(data));
endinterface
module empty_member (input logic a, output logic b);
    ;
    assign b = a;
endmodule
module explicit_import (input logic in_sig, output logic out_sig);
    import pkgb::add;
    parameter int VAL = add(1);
    assign out_sig = in_sig;
endmodule
module wildcard_import (input logic din, output logic dout);
    import pkga::*;
    logic [WIDTH-1:0] tmp;
    assign tmp = {WIDTH{din}};
    assign dout = tmp[0];
endmodule
module cont_assign (input wire [3:0] in_bus, output wire [3:0] out_bus);
    assign out_bus = in_bus;
endmodule
module alias_example (input wire a, output wire b);
    wire c;
    alias a = c;
    assign b = c;
endmodule
module gen_example (input wire [3:0] in_vec, output wire [3:0] out_vec);
    genvar i;
    generate
        for (i = 0; i < 4; i++) begin : g
            assign out_vec[i] = in_vec[i];
        end
    endgenerate
endmodule
module elab_tasks (input wire sig_in, output wire sig_out);
    $info("Elaboration info");
    $warning("Elaboration warning");
    assign sig_out = sig_in;
endmodule
module implicit_net_example (input wire a_in, output wire b_out);
    assign undeclared_net = a_in;
    assign b_out = undeclared_net;
endmodule
