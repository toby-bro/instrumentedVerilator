`default_nettype none
module comb_logic(
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic [3:0] y
);
    always_comb begin
        y = (a & b) ^ (a | b);
    end
endmodule
module seq_reg(
    input  logic        clk,
    input  logic        rst_n,
    input  logic [7:0]  d,
    output logic [7:0]  q
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            q <= '0;
        else
            q <= d;
    end
endmodule
module gen_param #(
    parameter int WIDTH     = 8,
    parameter int REPLICATE = 4
)(
    input  logic [WIDTH-1:0]                   in_bus,
    output logic [(WIDTH*REPLICATE)-1:0]       out_bus
);
    genvar i;
    generate
        for (i = 0; i < REPLICATE; i++) begin : g_rep
            assign out_bus[(i+1)*WIDTH-1 -: WIDTH] = in_bus;
        end
    endgenerate
endmodule
module struct_union(
    input  logic [15:0] bus_in,
    output logic [7:0]  lower_byte
);
    typedef struct packed {
        logic [7:0] low;
        logic [7:0] high;
    } word_t;
    word_t w;
    always_comb begin
        w = bus_in;
        lower_byte = w.low;
    end
endmodule
module assert_demo(
    input  logic clk,
    input  logic rst_n,
    input  logic val,
    output logic ready
);
    always_comb ready = val;
    property val_implies_ready;
        @(posedge clk) disable iff (!rst_n) (val |-> ready);
    endproperty
    assert property(val_implies_ready);
endmodule
module class_demo(
    input  logic [7:0] in_data,
    output logic [7:0] out_sum
);
    class adder_c;
        function automatic logic [7:0] plus1(input logic [7:0] d);
            plus1 = d + 8'd1;
        endfunction
    endclass
    adder_c my_adder;
    initial begin
        my_adder = new();
        out_sum  = my_adder.plus1(in_data);
    end
endmodule
`default_nettype wire
