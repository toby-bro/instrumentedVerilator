package Pkg;
    parameter int P = 10;
    typedef union packed { logic [3:0] u; logic [1:0] v; } u_t;
    function int pkg_fn(input int a);
        return a * P;
    endfunction
endpackage
import Pkg::*;
interface IntfIf(input logic clk);
    logic sig;
    modport slave (input sig);
endinterface
module FuncModule(input logic clk, input logic rst, input logic [3:0] in1, output logic [3:0] out1);
    typedef enum logic [1:0] { ST0, ST1, ST2 } state_t;
    typedef struct packed { logic [3:0] data; state_t st; } packet_t;
    function logic [3:0] process_packet(input packet_t p);
        return p.data + p.st;
    endfunction
    logic [3:0] data_reg;
    always_ff @(posedge clk) begin
        if (rst) data_reg <= 4'd0;
        else data_reg <= process_packet(packet_t'{data:in1, st:ST1});
    end
    assign out1 = data_reg;
endmodule
module IntfMod(input logic clk, IntfIf.slave iport, output logic out_sig);
    assign out_sig = iport.sig;
endmodule
module GenMod(input logic en, input logic [7:0] a, output logic [15:0] sum);
    logic [7:0] regs [3:0];
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : GEN
            always_comb begin
                if (en) regs[i] = a + i;
                else regs[i] = a - i;
            end
        end
    endgenerate
    assign sum = regs[0] + regs[1] + regs[2] + regs[3];
endmodule
module ArrayMod(input logic [1:0] a, input logic [1:0] b, output logic [3:0] y);
    logic [1:0] arr_unpacked [3:0];
    logic [1:0][3:0] arr_packed;
    always_comb begin
        arr_unpacked[2] = a;
        arr_packed[1][1] = b[1];
        arr_packed[1][0] = b[0];
    end
    assign y = {arr_unpacked[2], arr_packed[1][1], arr_packed[1][0]};
endmodule
module PkgMod(input logic [3:0] in_pkg, output logic [7:0] out_pkg);
    assign out_pkg = pkg_fn(in_pkg);
endmodule
module ClassMod(input logic clk, input logic start, output logic done);
    class C;
        int count;
        function new(); count = 0; endfunction
        function void incr(); count++; endfunction
        function int get(); return count; endfunction
    endclass
    C c_inst;
    always_ff @(posedge clk) begin
        if (start) c_inst = new;
        else if (c_inst != null) begin
            c_inst.incr();
            done <= (c_inst.get() > 5);
        end
    end
endmodule
module ParamMod #(parameter WIDTH = 8) (input logic [WIDTH-1:0] in_p, output logic [WIDTH-1:0] out_p);
    localparam int HALF = WIDTH/2;
    assign out_p = { in_p[WIDTH-1 -: HALF], in_p[HALF-1:0] };
endmodule
module TaskMod(input logic [3:0] a, input logic [3:0] b, output logic [4:0] c);
    task automatic do_task(input logic [3:0] x, output logic [3:0] y);
        y = x + 1;
    endtask
    function automatic logic [3:0] do_fn(input logic [3:0] z);
        return z + 2;
    endfunction
    always_comb begin
        logic [3:0] tmp;
        do_task(a, tmp);
        c = do_fn(tmp) + b;
    end
endmodule
module AssertMod(input logic a, input logic b, output logic c);
    assign c = a & b;
    always_comb begin
        assert (c == (a & b));
    end
endmodule
module CoverMod(input logic [1:0] a_in, input logic clk, output logic [1:0] a_out);
    covergroup cg @(posedge clk);
        cp : coverpoint a_in;
    endgroup
    cg cg_inst = new();
    assign a_out = a_in;
endmodule
module UnionMod(input logic [1:0] in_u, output logic [1:0] out_u);
    typedef union packed { logic [1:0] a; logic [0:0] b; } u_t;
    u_t u;
    always_comb begin
        u.a = in_u;
    end
    assign out_u = u.b;
endmodule
module CaseMod(input logic [3:0] sel, input logic data, output logic out_c);
    always_comb begin
        case (sel)
            4'd0: out_c = data;
            4'd1: out_c = ~data;
            default: out_c = data & sel[0];
        endcase
    end
endmodule
module ClockBlockMod(input logic clk, input logic rst, output logic cb_sig);
    clocking cb @(posedge clk);
        input rst;
        output cb_sig;
    endclocking
    assign cb_sig = rst;
endmodule
