package util_pkg;
    typedef enum logic [1:0] {IDLE = 2'b00, RUN = 2'b01, STOP = 2'b10} state_e;
    typedef struct packed {
        logic [7:0] a;
        logic [7:0] b;
    } pair_t;
    class simple_class;
        rand logic [7:0] data;
        function new();
            data = 0;
        endfunction
        function logic [7:0] get();
            return data;
        endfunction
    endclass
endpackage
interface simple_if (input logic clk);
    logic [7:0] data;
    modport m (output data, input clk);
    modport s (input  data, input clk);
    clocking cb @(posedge clk);
        default input #0 output #0;
        output data;
    endclocking
endinterface
module enum_module (
    input  logic [1:0] sel,
    output logic       y
);
    import util_pkg::*;
    state_e state_d;
    always_comb begin
        case (sel)
            IDLE   : y = 1'b0;
            RUN,
            STOP   : y = 1'b1;
            default: y = 1'b0;
        endcase
        state_d = IDLE;
    end
endmodule
module struct_module (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] sum
);
    import util_pkg::*;
    pair_t p;
    always_comb begin
        p.a = a;
        p.b = b;
        sum = p.a + p.b;
    end
endmodule
module class_module (
    input  logic       clk,
    output logic [7:0] dout
);
    import util_pkg::*;
    simple_class sc;
    logic [7:0] d;
    always_ff @(posedge clk) begin
        sc = new();
        d  = sc.get();
        sc.data = d;
        dout <= sc.data;
    end
endmodule
module union_module (
    input  logic [15:0] in_data,
    output logic [7:0]  upper
);
    typedef union packed {
        logic [15:0] word;
        struct packed {
            logic [7:0] lo;
            logic [7:0] hi;
        } bytes;
    } u_t;
    u_t u;
    always_comb begin
        u.word = in_data;
        upper  = u.bytes.hi;
    end
endmodule
module generate_module #(
    parameter int WIDTH = 4
) (
    input  logic [WIDTH-1:0] in_bus,
    output logic [WIDTH-1:0] out_bus
);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : gen_blk
            assign out_bus[i] = ~in_bus[i];
        end
    endgenerate
endmodule
module foreach_module (
    input  logic [3:0] in_bus,
    output logic       parity
);
    logic [2:0] foo [4];
    int i;
    always_comb begin
        parity = 1'b0;
        foreach (foo[i]) begin
            foo[i] = {2'b00, in_bus[i]};
            parity ^= foo[i][0];
        end
    end
endmodule
module dpi_module (
    input  logic [31:0] a,
    output logic [31:0] b
);
    import "DPI-C" function int c_function (input int x);
    always_comb begin
        b = c_function(a);
    end
endmodule
module iface_local_module (
    input  logic       clk,
    input  logic [7:0] din,
    output logic [7:0] dout
);
    simple_if if_local(clk);
    always_comb begin
        if_local.data = din;
        dout = if_local.data;
    end
endmodule
