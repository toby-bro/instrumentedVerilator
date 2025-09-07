module DTypeModule #(parameter int WIDTH = 8) (
    input  logic [WIDTH-1:0] in_a,
    input  logic signed [7:0]    in_b,
    output logic [WIDTH-1:0] out_c
);
    logic signed [WIDTH-1:0] signed_a;
    always_comb begin
        signed_a = in_a;
        out_c     = signed_a + in_b;
    end
endmodule
module ParamTypeModule #(parameter int N = 4) (
    input  logic [N-1:0] in_bus,
    output logic [N-1:0] out_bus
);
    typedef logic [N*2-1:0] big_t;
    big_t local_var;
    always_comb begin
        local_var = {in_bus, in_bus};
        out_bus   = local_var[N-1:0];
    end
endmodule
module EnumStructUnionModule (
    input  logic       sel,
    input  logic [3:0] io,
    output logic [3:0] oo
);
    typedef enum logic [1:0] { RED = 2'b00, GREEN = 2'b01, BLUE = 2'b10 } color_t;
    struct packed { logic [3:0] x; logic [3:0] y; } point_t;
    union packed { logic [7:0] u; point_t pt; } uni_t;
    color_t    c;
    point_t    p;
    uni_t      uvar;
    always_comb begin
        c        = sel ? GREEN : RED;
        p.x      = io;
        p.y      = 4'hF;
        uvar.pt  = p;
        oo       = uvar.u[3:0];
    end
endmodule
module ClassModule (
    input  logic       clk,
    input  logic       rst,
    output logic [3:0] out
);
    class Base;
        virtual function int f(input int a);
            return a;
        endfunction
    endclass
    class Derived extends Base;
        function int f(input int a);
            return a * 2;
        endfunction
    endclass
    Base    base_ptr;
    Derived der_obj;
    int     result;
    always_ff @(posedge clk) begin
        base_ptr = new();
        der_obj  = new();
        result   = base_ptr.f(1) + der_obj.f(2);
        out      <= result[3:0];
    end
endmodule
module ConstraintClassModule (
    input  logic       clk,
    output logic [7:0] val
);
    class RandClass;
        rand logic [3:0] a;
        rand logic [3:0] b;
        constraint myc { a < b; }
    endclass
    RandClass rc;
    logic [7:0] tmp;
    always_ff @(posedge clk) begin
        rc     = new();
        rc.randomize();
        tmp    = {rc.a, rc.b};
        val    <= tmp;
    end
endmodule
module AssignModule (
    input  logic        en,
    input  logic [7:0]  in1,
    input  logic [7:0]  in2,
    output logic [7:0]  out1,
    output logic [7:0]  out2
);
    wire  [7:0] wsum;
    reg   [7:0] rsum;
    assign wsum = in1 + in2;
    always_ff @(posedge en) begin
        rsum <= in1 - in2;
    end
    always_comb begin
        out1 = wsum;
        out2 = rsum;
    end
endmodule
module MemberSelModule (
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic [1:0] sel
);
    struct packed { logic [1:0] f1; logic [1:0] f2; } s;
    always_comb begin
        s.f1 = a[1:0];
        s.f2 = b[3:2];
        sel  = s.f1 + s.f2;
    end
endmodule
module TaskFunctionModule (
    input  logic [3:0] din,
    output logic [3:0] dout
);
    function automatic logic [3:0] fun(input logic [3:0] x);
        return x + 4'h1;
    endfunction
    task automatic tsk(input logic [3:0] x, output logic [3:0] y);
        y = x - 4'h1;
    endtask
    always_comb begin
        dout = fun(din);
        tsk(din, dout);
    end
endmodule
interface MyIf(input logic clk);
    logic sig;
    modport mp (input clk, output sig);
endinterface
module InterfaceUser (
    interface MyIf.mp intf,
    input     logic       en,
    output    logic       sig_out
);
    always_ff @(posedge intf.clk) begin
        if (en)
            intf.sig <= 1;
        else
            intf.sig <= 0;
        sig_out <= intf.sig;
    end
endmodule
module VirtualClassModule (
    input  logic       clk,
    output logic [3:0] out
);
    virtual class ICls;
        pure virtual function int proc(input int x);
    endclass
    class CImpl extends ICls;
        function int proc(input int x);
            return x * x;
        endfunction
    endclass
    CImpl obj;
    int   val;
    always_ff @(posedge clk) begin
        obj = new();
        val = obj.proc(3);
        out <= val[3:0];
    end
endmodule
module TypedefModule (
    input  logic [7:0] in0,
    output logic [7:0] out0
);
    typedef logic [3:0] small_t;
    small_t st;
    always_comb begin
        st   = in0[3:0];
        out0 = {4'h0, st};
    end
endmodule
