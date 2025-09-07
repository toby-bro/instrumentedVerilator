interface bus_if #(parameter int WIDTH = 8) ();
    logic [WIDTH-1:0] data;
    modport host (output data);
    modport dev  (input  data);
endinterface
module param_width #(parameter int W = 4)
    (input  logic [W-1:0] a,
     output logic [W-1:0] y);
    generate
        if (W >= 8) begin : gen_big
            assign y = a & {W{1'b1}};
        end else begin : gen_small
            assign y = a;
        end
        genvar i;
        for (i = 0; i < W; i++) begin : bit_loop
            logic w_local;
            assign w_local = a[i];
        end
    endgenerate
endmodule
module param_type #(parameter type T = logic,
                    parameter T VAL = '0)
    (input  T in,
     output T out);
    assign out = in ^ VAL;
endmodule
module param_string #(parameter string NAME = "foo")
    (input  logic in,
     output logic out);
    assign out = in;  
endmodule
module bus_host #(parameter int WIDTH = 8)
    (bus_if.host b,
     input  logic [WIDTH-1:0] in,
     output logic [WIDTH-1:0] out);
    assign b.data = in;
    assign out   = b.data;
endmodule
module bus_dev #(parameter int WIDTH = 8)
    (bus_if.dev b,
     input  logic dummy,
     output logic [WIDTH-1:0] out);
    assign out = b.data;
endmodule
module gen_case #(parameter int SEL = 0,
                  parameter int WIDTH = 8)
    (input  logic [WIDTH-1:0] in,
     output logic [WIDTH-1:0] out);
    generate
        case (SEL)
            0: assign out = in;
            1: assign out = ~in;
            default: assign out = {WIDTH{1'b0}};
        endcase
    endgenerate
endmodule
class my_container #(parameter int DEPTH = 2,
                     parameter type U = int);
    U buffer[DEPTH];
    function void push(input U val);
        buffer[0] = val;
    endfunction
    function U get();
        return buffer[0];
    endfunction
endclass
module class_user #(parameter int DEPTH = 2,
                    parameter type U = int)
    (input  U in,
     output U out);
    my_container#(DEPTH, U) obj;
    initial begin
        obj = new();
    end
    always_comb begin
        obj.push(in);
        out = obj.get();
    end
endmodule
module array_param
    #(parameter int LIST [0:2] = '{1,2,3})
    (input  logic clk,
     output logic [31:0] first);
    assign first = LIST[0];
endmodule
module system_mod #(parameter int WIDTH = 16)
    (input  logic [WIDTH-1:0] in,
     output logic [WIDTH-1:0] out);
    bus_if #(.WIDTH(WIDTH)) b();
    logic [WIDTH-1:0] inter;
    logic [WIDTH-1:0] tmp;
    bus_host #(.WIDTH(WIDTH)) h (.b(b), .in(in),      .out(inter));
    bus_dev  #(.WIDTH(WIDTH)) d (.b(b), .dummy(1'b0), .out(tmp));
    assign out = tmp ^ inter;  
endmodule
module override_examples
    (input  logic [7:0] in,
     output logic [7:0] out_pw,
     output logic [7:0] out_pt,
     output logic       out_ps);
    param_width  #(.W(8))                u_pw (.a(in),            .y(out_pw));
    param_type   #(.T(logic [7:0]), .VAL(8'hAA))
                                      u_pt (.in(in),            .out(out_pt));
    param_string #(.NAME("custom"))  u_ps (.in(out_pt[0]),      .out(out_ps));
endmodule
