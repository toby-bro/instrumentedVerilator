package PkgUtils;
    typedef logic [7:0] byte_t;
    localparam int LEVEL = 1;
endpackage
package PkgMath;
    import PkgUtils::*;
    function int sum(int a, int b);
        return a + b;
    endfunction
    export "DPI-C" function sum;
endpackage
import PkgUtils::*;
import PkgMath::*;
interface IfaceExample(input logic clk);
    logic flag;
    modport mp(input clk, output flag);
    function void trigger();
        flag = 1;
    endfunction
endinterface
class LinkCellsGraph;
    function new();
    endfunction
    function void loopsMessageCb(string vertexName, int weight);
    endfunction
endclass
class LinkCellsVertex;
    string name;
    function new(string nm);
        name = nm;
    endfunction
    function int rankAdder();
        return 1;
    endfunction
endclass
class LibraryVertex;
    function new();
    endfunction
    function string getName();
        return "*LIBRARY*";
    endfunction
endclass
module ModuleA #(parameter int WIDTH = 8) (
    input logic clk,
    input logic rst_n,
    input logic [WIDTH-1:0] data_in,
    output logic data_out
);
    localparam int MAXCNT = WIDTH * 2;
    logic [WIDTH-1:0] regA;
    logic [3:0] array_var[0:7];
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) regA <= '0;
        else regA <= data_in;
    end
    assign data_out = &regA;
endmodule
module ModuleB (
    input logic [3:0] sig_in,
    output logic [1:0] sig_out
);
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : genblock
            logic bit_i;
            assign bit_i = sig_in[i];
            assign sig_out = bit_i ? i[1:0] : sig_out;
        end
    endgenerate
endmodule
module Submodule (
    input logic x,
    input logic y,
    output logic z
);
    assign z = x & y;
endmodule
module ModuleF (
    input logic x,
    input logic y,
    output logic z
);
    Submodule u_sub(.*);
endmodule
module ModuleC (
    input logic clk,
    input logic rst,
    output logic ready
);
    IfaceExample if_inst(.clk(clk));
    virtual IfaceExample vif = if_inst;
    always_comb begin
        ready = vif.flag;
    end
endmodule
module ModuleD;
    import PkgMath::*;
    logic [7:0] sum_val;
    output logic overflow;
    always_comb begin
        sum_val = sum(8'd5, 8'd10);
    end
    assign overflow = (sum_val > 8'hFF);
endmodule
module ModuleE (
    input logic a,
    input logic b,
    output logic c
);
    ModuleA u1 (a, b, 4'b1010, c);
    ModuleA #(.WIDTH(4)) u2 (
        .clk(a),
        .rst_n(b),
        .data_in(4'b0101),
        .data_out(c)
    );
endmodule
module UseClass (
    input logic in,
    output logic out
);
    class C;
        function logic process(logic x);
            return !x;
        endfunction
    endclass
    C c_inst;
    always_comb begin
        c_inst = new();
        out = c_inst.process(in);
    end
endmodule
module ModuleGraph (
    input logic clk,
    output logic valid
);
    LinkCellsGraph graph;
    LinkCellsVertex vtx;
    LibraryVertex libv;
    always_comb begin
        graph = new();
        vtx = new("vertexName");
        libv = new();
        valid = (vtx.rankAdder() > 0);
    end
endmodule
bind ModuleE u2 ModuleB bind_inst (
    .sig_in(a),
    .sig_out(c)
);
config CFG1;
    design ModuleA;
    default liblist work;
    instance inst1: ModuleB;
    use work;
endconfig
