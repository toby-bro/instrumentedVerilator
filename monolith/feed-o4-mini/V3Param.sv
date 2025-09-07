package pkg1;
    typedef struct packed { logic [3:0] a; logic [3:0] b; } mystruct_t;
    typedef enum logic [1:0] { S0, S1, S2 } state_t;
    typedef union packed { logic [7:0] u1; logic [3:0][1:0] u2; } myunion_t;
endpackage
interface iface1 (input logic clk);
    logic data;
    modport mp (input data);
endinterface
class cls1;
    int a;
    function void f();
        a = 5;
    endfunction
endclass
module param_mod
    #(parameter int P1 = 8, parameter real PR = 1.5, parameter string PS = "abc")
    (input  logic [P1-1:0] in1,
     output logic [P1-1:0] out1);
    assign out1 = in1;
endmodule
module param_override
    #(parameter int PX = 4)
    (input  logic [PX-1:0] in2,
     output logic [PX-1:0] out2);
    assign out2 = in2;
endmodule
module override_mod
    (input  logic [5:0] a,
     output logic [5:0] b);
    param_override #(.PX(6)) inst1 (.in2(a), .out2(b));
endmodule
module type_param_mod
    #(parameter type T = logic [7:0])
    (input  T in,
     output T out);
    assign out = in;
endmodule
module use_type_param
    (input  logic [7:0] x,
     output logic [7:0] y);
    type_param_mod #(.T(logic signed [7:0])) inst2 (.in(x), .out(y));
endmodule
module use_iface
    (input  logic clk,
     output logic d_out);
    iface1 if_inst (.clk(clk));
    assign d_out = if_inst.data;
endmodule
module use_virtual
    (input  logic dummy,
     iface1 vif,
     output logic vdata);
    assign vif.clk = dummy;
    assign vdata = vif.data;
endmodule
module gen_if_mod
    #(parameter bit SEL = 1)
    (input  logic [3:0] in3,
     output logic [3:0] out3);
    generate
        if (SEL) begin : IF1
            assign out3 = in3;
        end else begin : IF2
            assign out3 = ~in3;
        end
    endgenerate
endmodule
module gen_for_mod
    (input  logic [3:0] din,
     output logic [3:0] dout);
    genvar j;
    generate
        for (j = 0; j < 4; j++) begin : loop
            assign dout[j] = din[j];
        end
    endgenerate
endmodule
module gen_case_mod
    #(parameter logic [1:0] SEL = 2'b00)
    (input  logic dummy,
     output logic [3:0] dout);
    generate
        case (SEL)
            2'b00: begin : C0
                assign dout = 4'b0001;
            end
            2'b01: begin : C1
                assign dout = 4'b0010;
            end
            default: begin : CDEF
                assign dout = 4'b1111;
            end
        endcase
    endgenerate
endmodule
module class_mod
    (input  logic clk,
     input  logic en,
     output logic [31:0] o);
    cls1 c_inst;
    always_comb begin
        if (en) begin
            c_inst = new();
            c_inst.f();
        end
        o = c_inst.a;
    end
endmodule
module localparam_mod
    (input  logic [1:0] sel,
     output logic [3:0] out);
    localparam logic [3:0] LP = 4'b1010;
    assign out = (sel == 2'b01) ? LP : 4'b0000;
endmodule
module child_par
    #(parameter int WIDTH = 1)
    (input  logic [WIDTH-1:0] x,
     output logic [WIDTH-1:0] y);
    assign y = x;
endmodule
module use_defparam
    (input  logic [3:0] p,
     output logic [3:0] q);
    child_par inst_child (.x(p), .y(q));
    defparam inst_child.WIDTH = 4;
endmodule
module unpack_mod
    (input  logic [3:0] arr_in [1:0],
     output logic [3:0] arr_out [1:0]);
    assign arr_out = arr_in;
endmodule
module mem_mod
    (input  logic        clk,
     input  logic        we,
     input  logic [3:0]  din,
     input  logic [1:0]  addr,
     output logic [3:0]  dout);
    logic [3:0] mem [0:3];
    always_ff @(posedge clk) if (we) mem[addr] <= din;
    assign dout = mem[addr];
endmodule
module enum_mod
    (input  pkg1::state_t state,
     output logic         out);
    assign out = (state == pkg1::S1);
endmodule
module use_pkg
    (input  pkg1::mystruct_t ms_in,
     output logic [4:0]    outp);
    assign outp = ms_in.a + ms_in.b;
endmodule
module struct_mod
    (input  pkg1::mystruct_t st_in,
     output logic         st_out);
    assign st_out = st_in.a & st_in.b;
endmodule
module use_union
    (input  pkg1::myunion_t u_in,
     output logic [7:0]    outu);
    assign outu = u_in.u1;
endmodule
