interface ifc #(parameter int W = 8) (input logic clk);
    logic [W-1:0] data;
    modport master (input clk, output data);
    modport slave  (input clk, input  data);
endinterface
module m_numeric #(parameter int WIDTH = 8, parameter int OFFSET = 1)
   (input  logic [WIDTH-1:0] a,
    output logic [WIDTH-1:0] y);
    assign y = a + OFFSET;
endmodule
module m_numeric_inst
   (input  logic [15:0] in,
    output logic [15:0] out);
    m_numeric #(.WIDTH(16), .OFFSET(-3)) u_num (.a(in), .y(out));
endmodule
module m_array #(parameter int SIZE = 4, parameter bit [SIZE-1:0] MASK = {SIZE{1'b1}})
   (input  logic [SIZE-1:0] a,
    output logic [SIZE-1:0] y);
    assign y = a & MASK;
endmodule
module m_type #(parameter type T = logic)
   (input  T a,
    output T y);
    assign y = a;
endmodule
module m_type_use
   (input  logic [31:0] in,
    output logic [31:0] out);
    m_type #(.T(logic [31:0])) u_type (.a(in), .y(out));
endmodule
module m_ifc_producer #(parameter int W = 8)
   (input  logic        clk,
    input  logic [W-1:0] in,
    ifc.master          intf,
    output logic [W-1:0] out);
    always_comb begin
        intf.data = in;
        out       = in;
    end
endmodule
module m_ifc_consumer #(parameter int W = 8)
   (input  logic       clk,
    ifc.slave          intf,
    output logic [W-1:0] out);
    assign out = intf.data;
endmodule
module m_ifc_top
   (input  logic       clk,
    input  logic [7:0] din,
    output logic [7:0] dout);
    ifc #(.W(8)) intf0 (.clk(clk));
    logic [7:0] p_out;
    logic [7:0] c_out;
    m_ifc_producer #(.W(8)) prod (.clk(clk), .in(din), .intf(intf0), .out(p_out));
    m_ifc_consumer #(.W(8)) cons (.clk(clk), .intf(intf0), .out(c_out));
    assign dout = p_out ^ c_out;
endmodule
module m_gen_if #(parameter bit USE_AND = 1)
   (input  logic a,
    input  logic b,
    output logic y);
    generate
        if (USE_AND) begin : g_and
            assign y = a & b;
        end else begin : g_or
            assign y = a | b;
        end
    endgenerate
endmodule
module m_gen_for #(parameter int N = 4)
   (input  logic [N-1:0] in,
    output logic [N-1:0] out);
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : g
            assign out[i] = in[i];
        end
    endgenerate
endmodule
module m_gen_case #(parameter int MODE = 0)
   (input  logic a,
    input  logic b,
    output logic y);
    generate
        case (MODE)
            0: begin : m0 assign y = a ^  b; end
            1: begin : m1 assign y = a ~^ b; end
            default: begin : m2 assign y = a | b; end
        endcase
    endgenerate
endmodule
module m_string #(parameter string NAME = "default")
   (input  logic i,
    output logic o);
    assign o = i;
endmodule
module m_string_inst
   (input  logic i,
    output logic o);
    m_string #(.NAME("specific")) u_str (.i(i), .o(o));
endmodule
class my_class #(parameter int P = 1);
    int value = P;
    function int get();
        return value;
    endfunction
endclass
module m_class
   (input  logic        clk,
    input  logic [7:0]  din,
    output logic [7:0]  dout);
    my_class #(5) obj;
    always_comb begin
        obj = new();
        dout = obj.get() + din + {7'b0, clk};
    end
endmodule
