package pkg_classes;
    timeunit 1ns;
    timeprecision 1ps;
    class MyClass;
        rand bit [7:0] data;
        function new();
            data = 8'hA5;
        endfunction
        function bit [7:0] get();
            return data;
        endfunction
    endclass
endpackage
module dpi_mod
    #(parameter int WIDTH = 32)
    (input  logic                  clk,
     input  logic [WIDTH-1:0]      a,
     input  logic [WIDTH-1:0]      b,
     output logic [WIDTH-1:0]      y (*verilator public*));
    timeunit 1ns;
    timeprecision 1ps;
    import "DPI-C" function int dpi_add (input int x, input int y);
    function int sv_mul (input int x, input int y_val);
        sv_mul = x * y_val;
    endfunction
    export "DPI-C" function sv_mul;
    always_ff @(posedge clk) begin
        int tmp;
        tmp = dpi_add(int'(a), int'(b)) + sv_mul(int'(a), int'(b));
        y <= tmp;
    end
endmodule
module cover_mod
    (input  logic clk,
     input  logic in_sig,
     output logic flag_out);
    timeunit 1ns;
    timeprecision 1ps;
    always_ff @(posedge clk)
        flag_out <= in_sig;
endmodule
module array_mod
    (input  logic  [3:0] sel,
     output logic [15:0] dout (*verilator public*));
    timeunit 1ns;
    timeprecision 1ps;
    typedef logic [7:0] byte_t;
    byte_t mem2d [0:3][0:3] (*verilator public*);
    localparam byte_t CONST_VEC [0:3] = '{8'h11, 8'h22, 8'h33, 8'h44};
    always_comb begin
        dout = {mem2d[sel[1:0]][sel[3:2]], 8'h00};
    end
endmodule
module class_pkg_usage_mod
    (input  logic       clk,
     input  logic [7:0] din,
     output logic [7:0] dout);
    timeunit 1ns;
    timeprecision 1ps;
    import pkg_classes::*;
    MyClass c;
    always_ff @(posedge clk) begin
        if (c == null) begin
            c <= new();
        end
        dout <= din ^ c.get();
    end
endmodule
module event_mod
    (input  logic clk,
     input  logic trigger,
     output logic toggled (*verilator public*));
    timeunit 1ns;
    timeprecision 1ps;
    event ev;
    always_ff @(posedge clk) begin
        if (trigger) -> ev;
    end
    always @(ev) begin
        toggled <= ~toggled;
    end
endmodule
