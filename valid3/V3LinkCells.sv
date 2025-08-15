package my_pkg;
    parameter int WIDTH = 8;
    function automatic logic [WIDTH-1:0] inc(logic [WIDTH-1:0] a);
        inc = a + 1;
    endfunction
endpackage
module sub_mod(input  logic x,
               output logic y);
    assign y = x;
endmodule
module sub_star(input  logic alpha,
                output logic beta);
    assign beta = alpha;
endmodule
module sub_pos(input  logic in1,
               input  logic in2,
               output logic out1);
    assign out1 = in1 & in2;
endmodule
interface bus_if #(parameter WIDTH = 8);
    logic clk;
    logic [WIDTH-1:0] data;
    modport master(input  clk,
                   output data);
    modport slave(input  clk,
                  input  data);
endinterface
module producer(bus_if.master bus,
                input  logic [7:0] in,
                output logic dummy);
    assign bus.data = in;
    assign dummy = 1'b0;
endmodule
module consumer(bus_if.slave bus,
                output logic [7:0] out,
                input  logic       dummy_in);
    assign out = bus.data ^ {8{dummy_in}};
endmodule
module parent_star(input  logic alpha,
                   output logic beta);
    sub_star u_sub_star(.*);
endmodule
module parent_pos(input  logic a,
                  input  logic b,
                  output logic res);
    sub_pos u_sub_pos(a, b, res);
endmodule
module star_connect(input  logic in,
                    output logic out);
    logic tmp_in, tmp_out;
    assign tmp_in = in;
    sub_mod u_sub(.x(tmp_in), .y(tmp_out));
    assign out = tmp_out;
endmodule
module recursive_mod #(parameter int DEPTH = 0,
                       parameter int MAX_DEPTH = 2)
                      (input  logic in,
                       output logic out);
    generate
        if (DEPTH < MAX_DEPTH) begin : gen_rec
            recursive_mod #(.DEPTH(DEPTH + 1), .MAX_DEPTH(MAX_DEPTH)) u_rec(.in(in), .out(out));
        end else begin : gen_base
            assign out = in;
        end
    endgenerate
endmodule
module target_mod(input  logic a,
                  output logic b,
                  output logic bound_out);
    assign b = a;
endmodule
module bound_mon(input  logic in,
                 output logic out);
    assign out = ~in;
endmodule
bind target_mod bound_mon bm_inst(.in(a), .out(bound_out));
module system_mod(input  logic       clk,
                  input  logic [7:0] din,
                  output logic [7:0] dout);
    bus_if #(8) bus();
    assign bus.clk = clk;
    logic dummy_link;
    producer prod(bus, din, dummy_link);
    consumer cons(bus, dout, dummy_link);
endmodule
module iface_parent(bus_if bus,
                    input  logic x,
                    output logic y);
    assign bus.data = x;
    assign y = bus.data;
endmodule
module interface_system(input  logic clk,
                        input  logic d,
                        output logic q);
    bus_if #(8) bus();
    assign bus.clk = clk;
    iface_parent ip(bus, d, q);
endmodule
module pkg_user(input  logic [my_pkg::WIDTH-1:0] in,
                output logic [my_pkg::WIDTH-1:0] out);
    import my_pkg::*;
    assign out = inc(in);
endmodule
class base_c;
    function int foo(); return 0; endfunction
endclass
class child_c extends base_c;
    function int foo(); return super.foo() + 1; endfunction
endclass
module class_user(input  logic clk,
                  output logic [31:0] val);
    child_c obj;
    always_comb begin
        obj = new();
        val = obj.foo() + clk;
    end
endmodule
