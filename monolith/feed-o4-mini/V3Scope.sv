module mod_always(input logic clk, input logic rst, input logic d, output logic q);
    always_ff @(posedge clk or posedge rst) begin
        if (rst) q <= 1'b0;
        else q <= d;
    end
endmodule
module mod_assign(input logic a, input logic b, output logic c);
    assign c = a & b;
endmodule
module mod_alias(input wire a, output logic b);
    alias a_alias = a;
    assign b = a_alias;
endmodule
module mod_block_scope(input logic in, output logic out);
    generate
        begin : scopeVar
            logic tmp;
            assign tmp = in;
        end
    endgenerate
    assign out = ~scopeVar.tmp;
endmodule
module mod_cfunc(input int v_in, output int v_out);
    import "DPI-C" function int cfunc(input int v);
    assign v_out = cfunc(v_in);
endmodule
module mod_ftask(input logic clk, input logic [7:0] in, output logic [7:0] out);
    function automatic logic [7:0] f(input logic [7:0] x);
        return x + 1;
    endfunction
    task automatic t(input logic [7:0] x, output logic [7:0] y);
        y = x + 2;
    endtask
    always_ff @(posedge clk) begin
        out <= f(in);
        t(in, out);
    end
endmodule
module mod_cover(input logic clk, input logic [3:0] in, output logic [3:0] out);
    assign out = in;
    covergroup CG @(posedge clk);
        coverpoint in;
    endgroup
    CG cg_inst = new();
endmodule
module mod_class(input logic clk, input logic [3:0] in, output logic [15:0] out);
    class MyClass;
        rand int a;
        function int mfunc(input int x);
            return a * x;
        endfunction
    endclass
    always_ff @(posedge clk) begin
        static MyClass c = new();
        c.a = in;
        out <= c.mfunc(in);
    end
endmodule
interface MyIf(input logic clk);
    wire sig;
    modport M(inout sig, input clk);
endinterface
module mod_interface(input MyIf.M iface, output logic sig_out);
    assign iface.sig = 1'b1;
    assign sig_out = iface.sig;
endmodule
module mod_if_wrapper(input logic clk, output logic sig_out);
    MyIf iface_inst(.clk(clk));
    mod_interface u_mod_interface(.iface(iface_inst.M), .sig_out(sig_out));
endmodule
module inner_mod(input logic a, output logic b);
    assign b = ~a;
endmodule
module mod_hier(input logic in, output logic out);
    inner_mod u0(.a(in), .b(out));
endmodule
module mod_generate(input logic [3:0] vec, output logic [3:0] out);
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : gen_blk
            assign out[i] = vec[i];
        end
    endgenerate
endmodule
