`timescale 1ns/1ps
`define WIDTH 8
`define USE_ADD
`define TEMP_MACRO 1
`undef TEMP_MACRO
module directive_usage #(
    parameter int WIDTH_P = `WIDTH
) (
    input  logic [WIDTH_P-1:0] a,
    output logic [WIDTH_P-1:0] y
);
`ifdef USE_ADD
    assign y = a + 1;
`else
    assign y = a;
`endif
endmodule
module always_blocks (
    input  logic clk,
    input  logic rst_n,
    input  logic [7:0] d,
    output logic [7:0] q
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            q <= '0;
        else
            q <= d;
    end
endmodule
module unique_case (
    input  logic [1:0] sel,
    input  logic [7:0] a, b, c,
    output logic [7:0] y
);
    always_comb begin
        unique case (sel)
            2'd0: y = a;
            2'd1: y = b;
            default: y = c;
        endcase
    end
endmodule
module assert_property_mod (
    input  logic clk,
    input  logic rst,
    input  logic a,
    input  logic b,
    output logic pass
);
    logic pass_int = 1'b1;
    property p_stable;
        @(posedge clk) disable iff (!rst) a |-> b;
    endproperty
    assert property (p_stable) else pass_int = 1'b0;
    assign pass = pass_int;
endmodule
module typed_defs (
    input  logic [3:0] in,
    output logic [3:0] out
);
    typedef struct packed {
        logic [1:0] a;
        logic [1:0] b;
    } my_struct_t;
    typedef union packed {
        logic        [3:0] u;
        my_struct_t        st;
    } my_union_t;
    my_struct_t s1;
    my_union_t u1;
    always_comb begin
        s1 = '{a: in[3:2], b: in[1:0]};
        u1.st = s1;
        out = u1.u;
    end
endmodule
module enum_usage (
    input  logic [1:0] in,
    output logic match
);
    typedef enum logic [1:0] {
        STATE_IDLE   = 2'd0,
        STATE_ACTIVE = 2'd1,
        STATE_ERROR  = 2'd2
    } state_t;
    state_t state;
    always_comb begin
        state = state_t'(in);
    end
    assign match = (state inside {STATE_IDLE, STATE_ACTIVE});
endmodule
module class_usage (
    input  logic trigger,
    output logic done
);
    class base_c;
        rand int data;
        function void set(int d);
            data = d;
        endfunction
    endclass
    class child_c extends base_c;
        function void set(int d);
            super.set(d);
        endfunction
    endclass
    child_c obj;
    always_comb begin
        if (trigger) begin
            obj = new();
            obj.set(1);
        end
    end
    assign done = trigger;
endmodule
module generate_block_mod (
    input  logic [3:0] in,
    output logic [3:0] out
);
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : gen_loop
            assign out[i] = in[i];
        end
    endgenerate
endmodule
