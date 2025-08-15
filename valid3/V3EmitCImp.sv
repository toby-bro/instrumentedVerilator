timeunit 1ns/1ps;
package my_struct_pkg;
    typedef struct {
        int unsigned x;
        int unsigned y;
    } my_unpacked_t;
endpackage
class simple_class;
    int unsigned a;
    int unsigned b;
    function new(int unsigned ia = 0, int unsigned ib = 0);
        a = ia;
        b = ib;
    endfunction
    function int unsigned sum();
        return a + b;
    endfunction
endclass
module param_static_m
    #(parameter WIDTH = 8,
      parameter logic [WIDTH-1:0] MASK = {WIDTH{1'b1}})
    (input  logic [WIDTH-1:0] din,
     output logic [WIDTH-1:0] dout);
    static logic [WIDTH-1:0] reg_static;
    event ev_trig;
    always_comb begin
        reg_static = din & MASK;
        dout       = reg_static;
        -> ev_trig;
    end
endmodule
module class_new_m
    (input  logic clk,
     input  logic rst,
     output logic [7:0] sum_out);
    simple_class current;
    simple_class next;
    always_ff @(posedge clk) begin
        if (rst) begin
            current = new(5, 7);
            next    = new(0, 0);
            sum_out <= 0;
        end else begin
            next    = new(current.a + 1, current.b + 1);
            current = next;
            sum_out <= current.sum()[7:0];
        end
    end
endmodule
module struct_enum_cov_m
    #(parameter int DEPTH = 4)
    (input  logic         clk,
     input  logic         rst_n,
     input  logic [255:0] din,
     output logic [255:0] dout);
    typedef struct packed {
        logic [127:0] upper;
        logic [127:0] lower;
    } wide_pair_t;
    wide_pair_t wpair;
    typedef enum logic [1:0] {IDLE=2'd0, BUSY=2'd1, DONE=2'd2} state_e;
    state_e state;
    import my_struct_pkg::*;
    my_unpacked_t unpacked_s;
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            state        <= IDLE;
            unpacked_s.x <= 0;
            unpacked_s.y <= 0;
            wpair.upper  <= 0;
            wpair.lower  <= 0;
            dout         <= 0;
        end else begin
            wpair.upper  <= din[255:128];
            wpair.lower  <= din[127:0];
            dout         <= {wpair.upper, wpair.lower};
            if (state == DONE)
                state <= IDLE;
            else
                state <= state_e'(state + 1);
            unpacked_s.x <= unpacked_s.x + 1;
            unpacked_s.y <= unpacked_s.y + 2;
        end
    end
endmodule
module large_array_m
    #(parameter int WORDS0 = 4,
      parameter int WORDS1 = 3)
    (input  logic                       clk,
     input  logic [7:0]                 wr_data,
     input  logic [$clog2(WORDS0)-1:0]  wr_addr0,
     input  logic [$clog2(WORDS1)-1:0]  wr_addr1,
     input  logic                       wr_en,
     output logic [7:0]                 rd_data);
    logic [7:0] mem [0:WORDS0-1][0:WORDS1-1];
    always_ff @(posedge clk) begin
        if (wr_en)
            mem[wr_addr0][wr_addr1] <= wr_data;
        rd_data <= mem[wr_addr0][wr_addr1];
    end
endmodule
import "DPI-C" function int sw_add (input int a, input int b);
module dpi_call_m
    (input  logic [31:0] in_a,
     input  logic [31:0] in_b,
     output logic [31:0] sum);
    always_comb sum = sw_add(in_a, in_b);
endmodule
