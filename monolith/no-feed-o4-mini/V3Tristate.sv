module mod_concat(input logic [3:0] a, input logic [3:0] b, output logic [8:0] out);
    assign out = {a, b, 1'b1};
endmodule
module mod_select_slice(input logic [7:0] data, output logic [3:0] slice, output logic bit0);
    assign slice = data[7:4];
    assign bit0  = data[0];
endmodule
module mod_conditional(input logic sel, input logic [3:0] d1, input logic [3:0] d2, output logic [3:0] out);
    assign out = sel ? d1 : d2;
endmodule
module mod_conditional_tristate(input logic en, input logic d, inout tri tri_pin);
    assign tri_pin = en ? d : 1'bz;
endmodule
module mod_bufif1(input logic en, input logic d, inout tri tri_pin);
    bufif1(tri_pin, d, en);
endmodule
module mod_bufif0(input logic en, input logic d, inout tri tri_pin);
    bufif0(tri_pin, d, en);
endmodule
module mod_pullup_down(inout wire pu, inout wire pd);
    pullup   (pu);
    pulldown (pd);
endmodule
module mod_strength(input wire a, input wire b, inout tri w0, inout tri w1);
    tri (weak0, strong1) w0;
    tri (strong0, weak1) w1;
    assign w0 = a;
    assign w1 = b;
endmodule
module mod_wand_wor(input wire a, input wire b, wand w_and, wor w_or);
    assign w_and = a;
    assign w_and = b;
    assign w_or  = a;
    assign w_or  = b;
endmodule
module mod_and_or(input logic a, input logic b, output logic and_out, output logic or_out);
    assign and_out = a & b;
    assign or_out  = a | b;
endmodule
module mod_bitwise_xor(input logic [3:0] x, output logic [3:0] y);
    assign y = x ^ 4'hF;
endmodule
module mod_caseeq(input logic [2:0] in, output logic eq, output logic neq);
    assign eq  = (in === 3'b010);
    assign neq = (in !== 3'b101);
endmodule
module mod_countones(input logic [7:0] data, output int ones);
    assign ones = $countones(data);
endmodule
module mod_generate_loop #(parameter WIDTH = 8)(input logic [WIDTH-1:0] in, output logic [WIDTH-1:0] out);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i = i + 1) begin : gen_loop
            assign out[i] = in[i];
        end
    endgenerate
endmodule
module mod_for_loop(input logic [3:0] in, input logic [3:0] mask, output logic [3:0] out);
    always @* begin
        integer i;
        for (i = 0; i < 4; i = i + 1) begin
            out[i] = in[i] & mask[i];
        end
    end
endmodule
module mod_function(input logic [3:0] a, output logic [7:0] y);
    function automatic logic [7:0] replicate(input logic [3:0] in);
        replicate = {in, in};
    endfunction
    assign y = replicate(a);
endmodule
