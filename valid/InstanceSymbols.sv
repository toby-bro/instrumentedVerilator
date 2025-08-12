interface simple_if;
    logic data;
    modport s (output data);
    modport m (input data);
endinterface
module clocked_reg(
    input  logic clk,
    input  logic rst,
    input  logic d_in,
    output logic q_out
);
    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            q_out <= 1'b0;
        else
            q_out <= d_in;
    end
endmodule
module interface_driver(
    input  logic in_a,
    output logic out_b
);
    simple_if bus();
    assign bus.data = in_a;
    assign out_b = in_a;
endmodule
module primitive_array_gate #(
    parameter int WIDTH = 4
)(
    input  logic in_a,
    input  logic in_b,
    output logic [WIDTH-1:0] y
);
    wire [WIDTH-1:0] t;
    and u_and(t[0], in_a, in_b);
    not u_not(y[0], t[0]);
    genvar i;
    generate
        for (i = 1; i < WIDTH; i++) begin : g_and_array
            and g_and(y[i], in_a, in_b);
        end
    endgenerate
endmodule
module param_vector_slice #(
    parameter int W = 8
)(
    input  logic [W-1:0] vec_in,
    output logic [W/2-1:0] vec_low,
    output logic [W/2-1:0] vec_high
);
    assign vec_low  = vec_in[W/2-1:0];
    assign vec_high = vec_in[W-1:W/2];
endmodule
module implicit_net_demo(
    input  logic sig_a,
    output logic sig_y
);
    wire undeclared_net;
    assign undeclared_net = sig_a;
    assign sig_y = sig_a & undeclared_net;
endmodule
module multidim_array_example #(
    parameter int X = 2,
    parameter int Y = 3
)(
    input  logic in_valid,
    input  logic [X*Y-1:0] flat_in,
    output logic [X-1:0][Y-1:0] matrix_out
);
    genvar ix, iy;
    generate
        for (ix = 0; ix < X; ix++) begin : g_x
            for (iy = 0; iy < Y; iy++) begin : g_y
                assign matrix_out[ix][iy] = in_valid & flat_in[iy + ix*Y];
            end
        end
    endgenerate
endmodule
module const_func_typedef(
    input  logic [7:0] data_in,
    output logic [7:0] data_out
);
    typedef logic [7:0] byte_t;
    function automatic byte_t swap_bits(input byte_t din);
        byte_t tmp;
        tmp = {din[3:0], din[7:4]};
        return tmp;
    endfunction
    assign data_out = swap_bits(data_in);
endmodule
