package pkg1;
    localparam int CONST_VAL = 1;
endpackage
package pkg2;
    typedef logic [3:0] mytype_t;
endpackage
interface bus_if (input logic clk);
    logic data;
    task automatic wr (input logic [3:0] d);
        data = d[0];
    endtask
    modport master (input clk, output data, export task wr (input logic [3:0] d));
    modport slave  (input clk, input data);
endinterface
primitive myudp (o, a, b);
    output o;
    input  a, b;
    table
           0 0 : 0;
           0 1 : 0;
           1 0 : 0;
           1 1 : 1;
    endtable
endprimitive
module m_empty (input logic in, output logic out);
    ;
    assign out = in;
endmodule
module m_assign_strength (input wire a, output wire b);
    assign (strong1, weak0) b = a;
endmodule
module m_implicit_net (input wire a, output wire b);
    assign b = a;
    assign c = a;
    alias b = c;
endmodule
module m_pkg_import (input logic x, output logic y);
    import pkg1::CONST_VAL;
    import pkg2::*;
    assign y = x ^ CONST_VAL;
endmodule
module m_gen_loop (input logic in, output logic [3:0] out);
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : g
            assign out[i] = in;
        end
    endgenerate
endmodule
