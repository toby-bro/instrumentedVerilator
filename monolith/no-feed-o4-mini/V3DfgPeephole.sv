module zero_extend(in, out);
    input  [3:0] in;
    output [7:0] out;
    assign out = {4'b0, in};
endmodule
module sign_extend(in, out);
    input  [3:0] in;
    output [7:0] out;
    assign out = {{4{in[3]}}, in};
endmodule
module unary_not(in, out);
    input  in;
    output out;
    assign out = !in;
endmodule
module bitwise_not(in, out);
    input  [7:0] in;
    output [7:0] out;
    assign out = ~in;
endmodule
module negate(in, out);
    input  signed [7:0] in;
    output signed [7:0] out;
    assign out = -in;
endmodule
module red_and(in, out);
    input  [7:0] in;
    output      out;
    assign out = &in;
endmodule
module red_or(in, out);
    input  [7:0] in;
    output      out;
    assign out = |in;
endmodule
module red_xor(in, out);
    input  [7:0] in;
    output      out;
    assign out = ^in;
endmodule
module logical_and_or(a, b, lando, lora);
    input       a, b;
    output      lando, lora;
    assign lando = a && b;
    assign lora  = a || b;
endmodule
module bitwise_and_or_xor(a, b, ando, oro, xoro);
    input  [3:0] a, b;
    output [3:0] ando, oro, xoro;
    assign ando = a & b;
    assign oro  = a | b;
    assign xoro = a ^ b;
endmodule
module arith_add_sub_mul(a, b, addo, subo, mulo);
    input  [7:0] a, b;
    output [7:0] addo, subo, mulo;
    assign addo = a + b;
    assign subo = a - b;
    assign mulo = a * b;
endmodule
module arith_div_mod(a, b, dio, mio);
    input  [7:0] a, b;
    output [7:0] dio, mio;
    assign dio = a / b;
    assign mio = a % b;
endmodule
module comparisons(a, b, eqo, neqo, gto, lto, gteo, lteo);
    input  [3:0] a, b;
    output      eqo, neqo, gto, lto, gteo, lteo;
    assign eqo  = (a == b);
    assign neqo = (a != b);
    assign gto  = (a > b);
    assign lto  = (a < b);
    assign gteo = (a >= b);
    assign lteo = (a <= b);
endmodule
module multiplex2(sel, d0, d1, y);
    input        sel;
    input  [3:0] d0, d1;
    output [3:0] y;
    assign y = sel ? d1 : d0;
endmodule
module replicate_concat_select(a, rep, cat, sel);
    input  [1:0] a;
    output [7:0] rep;
    output [3:0] cat;
    output [1:0] sel;
    assign rep = {4{a}};
    assign cat = {a, a};
    assign sel = rep[5:4];
endmodule
module shifts(a, sh, sl, sr, srs);
    input  [7:0] a;
    input  [2:0] sh;
    output [7:0] sl, sr, srs;
    assign sl  = a << sh;
    assign sr  = a >> sh;
    assign srs = a >>> sh;
endmodule
module nested_concat(a, b, c, y);
    input  [3:0] a, b, c;
    output [11:0] y;
    assign y = {a, {b, c}};
endmodule
module complex_expr(a, b, c, y);
    input  [3:0] a, b, c;
    output [3:0] y;
    assign y = a & (b | c);
endmodule
module bit_slicing(a, lo, hi);
    input  [7:0] a;
    output [3:0] lo, hi;
    assign lo = a[3:0];
    assign hi = a[7:4];
endmodule
module array_select(arr, idx, y);
    input  [7:0] arr [3:0];
    input  [1:0] idx;
    output [7:0] y;
    assign y = arr[idx];
endmodule
module nested_mux(sel1, sel2, a, b, c, y);
    input       sel1, sel2;
    input  [3:0] a, b, c;
    output [3:0] y;
    assign y = sel1 ? (sel2 ? a : b) : c;
endmodule
module multi_concat(a, b, c, y);
    input  [1:0] a, b, c;
    output [5:0] y;
    assign y = {a, b, c};
endmodule
module zero_reduce_concat(in, out);
    input  [3:0] in;
    output       out;
    wire   [4:0] tmp;
    assign tmp = {1'b0, in};
    assign out = &tmp;
endmodule
module generate_loop #(parameter N = 4)(in, out);
    input  [N-1:0] in;
    output [N-1:0] out;
    genvar i;
    generate for (i = 0; i < N; i = i + 1) begin : gl
        assign out[i] = in[i];
    end endgenerate
endmodule
function [7:0] f_add(input [7:0] x, input [7:0] y);
    begin
        f_add = x + y;
    end
endfunction
module functional_sum(a, b, y);
    input  [7:0] a, b;
    output [7:0] y;
    assign y = f_add(a, b);
endmodule
module prevent_optimization(in, out);
    input  [3:0] in;
    output [3:0] out;
    wire   [7:0] tmp;
    assign tmp = {{4{in[3]}}, in} + {4'b0, in};
    assign out = tmp[3:0] & (in ^ in);
endmodule
