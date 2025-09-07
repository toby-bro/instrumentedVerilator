`timescale 1ns/1ps
package pkg_example;
   typedef enum logic [1:0] {RED=0, GREEN=1, BLUE=2, BLACK=3} color_e;
   parameter string STR = "hello";
   class util_c;
      int id;
      function new(int i); id = i; endfunction
   endclass
endpackage
module pkg_mod
    #(parameter WIDTH = 8)
    (input  logic                clk,
     input  logic [WIDTH-1:0]    in_data,
     output logic [WIDTH-1:0]    out_data);
    import pkg_example::*;
    parameter string PUBLIC_STR = STR;
    logic [WIDTH-1:0] pub_reg;
    logic [3:0] multi_arr [0:1][0:2];
    always_comb begin
        pub_reg          = in_data;
        multi_arr[0][0]  = in_data[3:0];
        out_data         = pub_reg;
    end
    always_ff @(posedge clk) begin
        util_c obj = new(5);
    end
endmodule
import "DPI-C" function int c_add(input int a, input int b);
module dpi_mod
    (input  logic [31:0] a,
     input  logic [31:0] b,
     output logic [31:0] y);
    logic [31:0] result;
    export "DPI-C" function sv_export;
    function void sv_export(input int x);
        result = x;
    endfunction
    always_comb begin
        result = c_add(a, b);
        y      = result;
    end
endmodule
module child_mod
    #(parameter W = 4)
    (input  logic [W-1:0] data_in,
     output logic [W-1:0] data_out);
    logic [W-1:0] shadow;
    always_comb begin
        shadow   = data_in;
        data_out = shadow;
    end
endmodule
module parent_mod
    (input  logic [7:0] data_in,
     output logic [7:0] data_out);
    child_mod #(.W(8)) u_child (.data_in(data_in), .data_out(data_out));
endmodule
module cover_mod
    (input logic clk,
     input logic sig_in,
     output logic sig_out);
    logic [3:0] cnt;
    always_ff @(posedge clk) begin
        cnt <= cnt + 1;
    end
    assign sig_out = cnt[0];
endmodule
module esc_mod
    (input  logic sig_in,
     output logic sig_out);
    logic \my.signal  ;
    logic [7:0] vec [0:1][0:1];
    always_comb begin
        \my.signal  = sig_in;
        vec[0][0]   = 8'hAA;
        sig_out     = \my.signal ;
    end
endmodule
