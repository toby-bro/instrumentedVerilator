interface simple_if;
    logic dat;
    modport mp (input dat);
endinterface
primitive udp_example(output out, input in1, input in2);
    table
        0 0 : 0;
        0 1 : 1;
        1 0 : 1;
        1 1 : 0;
    endtable
endprimitive
module mod_constraint(input logic [3:0] in, output logic [3:0] out);
    class rand_class;
        rand bit [3:0] val;
        constraint dist_c { val dist { 0 := 1, 1 := 1, 2 :/ 2 }; }
        constraint soft_c { soft val < 10; }
        constraint solve_c { solve val before val; }
    endclass
    rand_class rc = new();
    always_comb out = in ^ rc.val;
endmodule
module mod_let_case(
    input  logic [3:0] sel,
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic       y
);
    let my_and (logic aa, logic bb) = aa & bb;
    always_comb begin
        case (sel)
            default: y = a | b;
            4'd0:    y = my_and(a, b);
            4'd1:    y = a ^ b;
        endcase
    end
endmodule
module mod_generate #(
    parameter WIDTH = 8
) (
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i = i + 1) begin : gen_loop
            assign out[i] = in[WIDTH-1-i];
        end
        if (WIDTH > 4) begin : wide_gen
            logic unused;
            assign unused = &in;
        end
    endgenerate
endmodule
module mod_task_public(
    input  logic clk,
    input  logic rst,
    output logic done
);
    logic [3:0] state;
    task automatic do_something(input logic [3:0] a, output logic [3:0] b);
        b = a + 1;
    endtask
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            state <= 0;
        end else begin
            do_something(state, state);
        end
    end
    assign done = (state == 4'd10);
endmodule
module mod_iface_ref(
    input  logic dummy,
    output logic o
);
    simple_if intf();
    assign intf.dat = dummy;
    assign o = intf.dat;
endmodule
module mod_sformatf(
    input  logic [7:0] din,
    output logic [7:0] dout
);
    string fmt_str = "Value=%0d";
    string result;
    always_comb begin
        result = $sformatf(fmt_str, din);
    end
    assign dout = din;
endmodule
module mod_dpi(
    input  logic [7:0] in,
    output logic [7:0] out
);
    function automatic byte unsigned add_one(input byte unsigned a);
        add_one = a + 1;
    endfunction
    export "DPI-C" function add_one;
    assign out = add_one(in);
endmodule
module mod_assert(
    input  logic clk,
    input  logic rst,
    input  logic in,
    output logic out
);
    assign out = in;
    property my_prop;
        @(posedge clk) disable iff (rst) $rose(in) |=> !in;
    endproperty
    assert property (my_prop);
endmodule
