package util_pkg;
    parameter int CONST_VAL = 32;
endpackage
module enum_struct_mod
#(parameter int WIDTH = 8)
(
    input  logic                 clk,
    input  logic [WIDTH-1:0]     din,
    output logic [WIDTH-1:0]     dout
);
    import util_pkg::*;
    typedef enum logic [1:0] {IDLE = 2'b00, RUN = 2'b01, STOP = 2'b10} state_t;
    state_t                      cur_state = IDLE;
    struct packed {
        logic [WIDTH-1:0] data;
        logic             flag;
    } s_a, s_b;
    typedef union packed {
        logic [WIDTH-1:0]                                   as_vec;
        struct packed {logic [WIDTH/2-1:0] lo; logic [WIDTH/2-1:0] hi;} split;
    } u_data_t;
    u_data_t u_word;
    function automatic logic [WIDTH-1:0] incr(input logic [WIDTH-1:0] v);
        incr = v + 1;
    endfunction
    function static logic [WIDTH-1:0] dec(input logic [WIDTH-1:0] v);
        dec = v - 1;
    endfunction
    task automatic swap(inout logic [WIDTH-1:0] a, b);
        logic [WIDTH-1:0] tmp = a;
        a = b;
        b = tmp;
    endtask
    always_ff @(posedge clk) begin
        s_a.data <= din;
        cur_state <= (cur_state == RUN) ? STOP : RUN;
        if (cur_state == RUN) begin
            swap(s_a.data, s_b.data);
            u_word.as_vec <= incr(s_a.data);
        end
    end
    assign dout = dec(u_word.as_vec);
endmodule
module generate_mod
#(parameter int DEPTH = 4, parameter int WIDTH = 16)
(
    input  logic             en,
    input  logic [WIDTH-1:0] in_bus,
    output logic [WIDTH-1:0] out_bus
);
    localparam USE_WIDE = (WIDTH > 8);
    generate
        if (USE_WIDE) begin
            logic [WIDTH-1:0] wide_reg;
            assign wide_reg = in_bus;
            assign out_bus  = wide_reg;
        end else begin
            logic [WIDTH-1:0] narrow_reg;
            assign narrow_reg = in_bus;
            assign out_bus    = narrow_reg;
        end
    endgenerate
    logic [WIDTH-1:0] mirrors [0:DEPTH-1];
    generate
        genvar i;
        for (i = 0; i < DEPTH; i = i + 1) begin
            logic [WIDTH-1:0] mirror_wire;
            assign mirror_wire = in_bus;
            assign mirrors[i]  = mirror_wire;
        end
    endgenerate
endmodule
module clocking_mod(
    input  logic clk,
    input  logic in_sig,
    output logic out_sig
);
    clocking cb @(posedge clk);
        default input  #1step output #2;
        input  in_sig;
        output out_sig;
    endclocking
    always_comb begin
        cb.out_sig = cb.in_sig;
    end
endmodule
module foreach_mod
#(parameter int SIZE = 8)
(
    input  logic            clk,
    input  logic [SIZE-1:0] din,
    output logic [SIZE-1:0] dout
);
    logic [SIZE-1:0] arr [0:3];
    always_ff @(posedge clk) begin
        if (din[0]) begin
            wait (din[0]);                       
        end
        repeat (1) begin                         
            foreach (arr[idx]) begin             
                arr[idx] <= din ^ idx;
            end
        end
        do begin                                 
            arr[1] <= din;
        end while (1'b0);
    end
    assign dout = arr[0];
endmodule
module attr_mod(
    input  logic clk,
    input  logic enable,
    output logic [7:0] q
);
    (* public_flat_rw, forceable, isolate_assignments, sformat, split_var, sc_bv *)
    logic [7:0] myvar = 8'h00;
    (* clocker *)     logic [7:0] clk_var;
    (* no_clocker *)  logic [7:0] noclk_var;
    string last_msg;
    always_ff @(posedge clk) begin
        if (enable) begin
            myvar      <= myvar + 8'h1;
            clk_var    <= myvar;
            noclk_var  <= clk_var;
            last_msg   <= $sformatf("val=%0d", myvar);  
        end
    end
    assign q = noclk_var;
endmodule
module dpi_mod(
    input  logic [31:0] in_val,
    output logic [31:0] out_val
);
    timeunit 1ns / 1ps;
    import "DPI-C" function int sv_clog2(input int a);
    function automatic int my_clog2(input int v);
        my_clog2 = sv_clog2(v);
    endfunction
    assign out_val = my_clog2(in_val);
endmodule
