module DfgConstModule(input logic [3:0] in, output logic [7:0] out);
    logic [7:0] constval;
    assign constval = 8'hA5;
    assign out = constval + in;
endmodule
module DfgSelModule(input logic [7:0] in, output logic [3:0] out);
    assign out = in[5:2];
endmodule
module DfgMuxModule(input logic [7:0] a, input logic [7:0] b, input logic sel, output logic [7:0] y);
    assign y = sel ? a : b;
endmodule
module DfgSplicePackedModule(input logic [3:0] in0, input logic [3:0] in1, output logic [7:0] out);
    assign out = {in0, in1};
endmodule
module DfgSpliceArrayModule(input logic [7:0] in [0:3], output logic [7:0] out [0:3]);
    genvar i;
    generate
        for (i = 0; i < 4; i++) begin : gen_splice
            assign out[i] = in[3-i];
        end
    endgenerate
endmodule
module DfgVertexHashModule(input logic [7:0] in, output logic [3:0] hash);
    assign hash = ^in;
endmodule
module DfgVertexEqualsModule(input logic [7:0] a, input logic [7:0] b, output logic eq);
    assign eq = (a == b);
endmodule
module DfgEdgeRelinkModule(input logic in, output logic out);
    logic mid;
    assign mid = in;
    assign out = mid;
endmodule
module DfgGraphParamCloneModule #(parameter WIDTH = 8) (input logic [WIDTH-1:0] in, output logic [WIDTH-1:0] out);
    assign out = in;
endmodule
module DfgGenCaseModule(input logic [1:0] sel, input logic [7:0] in, output logic [7:0] out);
    always_comb begin
        case (sel)
            2'b00: out = in;
            2'b01: out = in + 1;
            2'b10: out = in - 1;
            default: out = in ^ 8'hFF;
        endcase
    end
endmodule
module DfgGenIfModule #(parameter USE_B = 0) (input logic [7:0] a, input logic [7:0] b, output logic [7:0] y);
    generate
        if (USE_B) begin
            assign y = b;
        end else begin
            assign y = a;
        end
    endgenerate
endmodule
module DfgFanoutCountModule(input logic [7:0] in, output logic [3:0] pop);
    assign pop = in[0] + in[1] + in[2] + in[3] + in[4] + in[5] + in[6] + in[7];
endmodule
module DfgClassInstModule(input logic [7:0] in, output logic [7:0] out);
    class Cl;
        int val;
        function new(int v);
            val = v;
        endfunction
        function int get();
            return val * 2;
        endfunction
    endclass
    always_comb begin
        Cl c = new(in);
        out = c.get();
    end
endmodule
module DfgDynamicArrayModule(input logic [3:0] size, input logic [7:0] in, output logic [7:0] out);
    logic [7:0] dyn_arr[];
    always_comb begin
        dyn_arr = new[size];
        if (size > 0) dyn_arr[0] = in;
        out = (size > 0) ? dyn_arr[size-1] : 8'h00;
    end
endmodule
