typedef struct unpacked { logic [1:0] a [0:1]; logic b; } unpacked_t;
typedef struct packed { logic [3:0] a; logic [1:0] b; } packed_t;
typedef logic [3:0] nibble_t;
module feature_unpacked_array(
    input  logic [1:0] in_arr [0:1],
    output logic [1:0] out_arr[0:1]
);
    always_comb begin
        out_arr[1][0] =  in_arr[0][0];
        out_arr[1][1] = ~in_arr[0][1];
    end
endmodule
module feature_packed_array(
    input  logic        some_cond,
    input  logic        some_input0,
    input  logic [2:0]  some_input1,
    input  logic [3:0]  in_var,
    output logic [3:0]  out_var
);
    always_comb begin
        if (some_cond) begin
            out_var = 4'b0;
        end else begin
            out_var[3]   = some_input0;
            out_var[2:0] = some_input1;
        end
    end
endmodule
module feature_struct_unpack(
    input  unpacked_t in_s,
    output unpacked_t out_s
);
    always_comb begin
        for (int i = 0; i < 2; i++) begin
            out_s.a[i] = in_s.a[i] ^ {2{in_s.b}};
        end
        out_s.b = in_s.a[0][1];
    end
endmodule
module feature_struct_packed(
    input  packed_t in_ps,
    output packed_t out_ps
);
    always_comb begin
        out_ps.a = in_ps.a;
        if (in_ps.a[3]) begin
            out_ps.b = in_ps.b;
        end else begin
            out_ps.b = ~in_ps.b;
        end
    end
endmodule
module feature_array_of_structs(
    input  packed_t in_arr[0:1],
    output logic   out_bit
);
    always_comb begin
        out_bit = in_arr[1].a[0] & in_arr[0].b[1];
    end
endmodule
module feature_bitfield(
    input  logic [7:0] in_byte,
    output logic       b0,
    output logic       b7,
    output logic [2:0] mid_bits
);
    always_comb begin
        b0       = in_byte[0];
        b7       = in_byte[7];
        mid_bits = in_byte[3:1];
    end
endmodule
module feature_multi_dim_packed(
    input  logic [1:0][3:0] in_2d,
    output logic [1:0][3:0] out_2d
);
    always_comb begin
        out_2d[0] = in_2d[1];
        out_2d[1] = in_2d[0];
    end
endmodule
module feature_typedef(
    input  nibble_t in_nib,
    output nibble_t out_nib
);
    always_comb begin
        out_nib = ~in_nib;
    end
endmodule
module feature_generate(
    input  logic [3:0] in_gen,
    output logic      out_gen[0:3]
);
    genvar i;
    generate
        for (i = 0; i < 4; i++) begin : gen_loop
            assign out_gen[i] = in_gen[i];
        end
    endgenerate
endmodule
module feature_function(
    input  logic [3:0] in_f,
    output logic [3:0] out_f
);
    function logic [3:0] swizzle;
        input logic [3:0] x;
        begin
            swizzle = {x[1:0], x[3:2]};
        end
    endfunction
    always_comb begin
        out_f = swizzle(in_f);
    end
endmodule
module feature_param #(
    parameter int WIDTH = 4
)(
    input  logic [WIDTH-1:0] in_p,
    output logic [WIDTH-1:0] out_p
);
    assign out_p = in_p << 1;
endmodule
