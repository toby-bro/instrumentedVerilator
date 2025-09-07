`timescale 1ns/1ps
module line_dir (input logic a, output logic b);
    `line 100 "foo.sv"
    assign b = a;
endmodule
module time_scale (input logic clk, output logic out);
    assign out = clk;
endmodule
module preproc (input logic en, output logic y);
    `define FOO
    `ifdef FOO
        assign y = en;
    `else
        assign y = ~en;
    `endif
endmodule
module ver_lint (input logic x, output logic z);
    /*verilator lint_off WIDTH*/
    wire [3:0] w = x ? 4'b1010 : 4'b0101;
    /*verilator lint_restore*/
    assign z = w[0];
endmodule
module ver_bad (input logic i, output logic o);
    /*verilator bad_pragma*/
    assign o = i;
endmodule
module prag_test (input logic din, output logic dout);
    (* keep = "true" *)
    logic temp;
    always @* temp = din;
    assign dout = temp;
endmodule
module parse_tag (input logic x, output logic y);
    /*verilator tag my_custom_tag*/
    assign y = x;
endmodule
module time_nums (input logic enable, output logic done);
    time t1 = 10ns;
    time t2 = 5_us;
    time t3 = 1_234ps;
    assign done = (enable && (t1 == t1)) ? 1'b1 : 1'b0;
endmodule
module sub #(parameter int WIDTH = 1) (input logic clk, output logic out);
    assign out = clk;
endmodule
module module_inst (input logic clk, output logic ready);
    sub #(.WIDTH(8)) inst0 (.clk(clk), .out(ready));
endmodule
module array_bracket (input logic en, output logic [1:0] dout);
    logic [7:0] mem [0:3];
    always @* begin
        mem[0] = en;
        dout = mem[0][1:0];
    end
endmodule
module param_scan (input logic a, output logic b);
    parameter int VAL = 4;
    assign b = (a << VAL);
endmodule
module type_eq (input int x, input int y, output logic eq, output logic seq);
    assign eq  = (x == y);
    assign seq = (x === y);
endmodule
module class_inst (input logic rst, output logic done);
    class C1; endclass
    C1 c_inst;
    always @* begin
        c_inst = new();
        done = rst;
    end
endmodule
module pipe_strength (input logic in, output logic out);
    supply1 sp1;
    pull0  p0;
    default pulltype (weak1, weak0) pulldown(in);
    assign out = in;
endmodule
module type_cast_new (input logic [3:0] a, output logic [3:0] b);
    class A; endclass
    A obj;
    logic [3:0] tmp;
    always @* begin
        obj = new();
        tmp = a;
        b = tmp;
    end
endmodule
module enum_struct_union (input logic sel, output logic [3:0] out);
    typedef enum logic [1:0] { A=2'd0, B=2'd1, C=2'd2 } myenum_t;
    typedef struct { logic [3:0] f1; myenum_t f2; } mystruct_t;
    typedef union { logic [3:0] u1; mystruct_t u2; } myunion_t;
    myunion_t u;
    always @* begin
        if (sel) begin
            u.u1 = 4'hA;
        end else begin
            u.u2.f1 = 4'h5;
            u.u2.f2 = C;
        end
        out = u.u1;
    end
endmodule
module generate_loop (input logic clk, output logic [7:0] bus);
    genvar i;
    generate
        for (i = 0; i < 8; i = i + 1) begin : genblk
            assign bus[i] = clk;
        end
    endgenerate
endmodule
module interface_inst (input logic clk, output logic out);
    interface_if uut (.clk(clk), .out(out));
endmodule
interface interface_if (input logic clk, output logic out);
    always @* out = clk;
endinterface
module fork_join (input logic start, output logic done);
    integer count;
    always @* begin
        fork
            count = start;
        join
        done = (count != 0);
    end
endmodule
module cover_directive (input logic en, output logic ok);
    covergroup cg @ (posedge en);
        coverpoint ok;
    endgroup
    cg cg_inst = new();
    always @* begin
        ok = en;
    end
endmodule
module event_control (input logic ev, output logic out);
    always @ (event ev) begin
        out = ev;
    end
endmodule
module wait_statement (input logic trig, output logic done);
    always @* begin
        wait (trig) done = 1;
    end
endmodule
module disable_statement (input logic ctl, output logic res);
    event ev;
    always @* begin
        disable ev;
        -> ev;
        res = ctl;
    end
endmodule
module covergroup_simple (input logic clk, output logic val);
    covergroup cg2;
        coverpoint clk;
    endgroup
    cg2 cg2_inst = new();
    always @* val = clk;
endmodule
module system_function (input logic [7:0] data, output logic valid);
    assign valid = $countones(data) > 0;
endmodule
module generate_if (input logic sel, output logic out);
    generate
        if (sel) begin
            assign out = 1;
        end else begin
            assign out = 0;
        end
    endgenerate
endmodule
