package util_pkg;
    typedef struct packed {
        logic [15:0] a;
        logic [7:0]  b;
    } my_struct_t;
    localparam logic [15:0] CONST_VAL = 16'h55AA;
    typedef logic [3:0] nibble_t;
    typedef nibble_t nibble_alias_t;
endpackage
module pkg_user (
    input  logic [15:0] in_data,
    output logic [15:0] out_data
);
    import util_pkg::*;
    my_struct_t local_s;
    always_comb begin
        local_s.a = in_data;
        local_s.b = in_data[7:0];
        out_data  = local_s.a + CONST_VAL;
    end
endmodule
module gen_array_module #(
    parameter int WIDTH = 8
)(
    input  logic [WIDTH-1:0]  in_bus,
    output logic [WIDTH-1:0]  out_bus
);
    genvar idx;
    generate
        for (idx = 0; idx < 4; idx++) begin : GEN_BLK
            logic [WIDTH-1:0] blk_sig;
            always_comb blk_sig = in_bus ^ idx;
        end
    endgenerate
    assign out_bus = GEN_BLK[2].blk_sig;
endmodule
module forward_enum_module (
    input  logic sel,
    output logic o_bit
);
    typedef enum logic [1:0] {ST_A, ST_B} state_fwd_t;
    state_fwd_t current_state;
    always_comb begin
        if (sel)
            current_state = ST_A;
        else
            current_state = ST_B;
    end
    assign o_bit = current_state[0];
endmodule
module nested_scope_module (
    input  logic [7:0]  din,
    output logic [7:0]  dout
);
    typedef byte byte_t;
    function automatic byte_t swap_nibbles (input byte_t v);
        swap_nibbles = {v[3:0], v[7:4]};
    endfunction
    always_comb begin
        dout = swap_nibbles(din);
    end
endmodule
module rand_style_module (
    input  logic clk,
    input  logic start,
    output logic done
);
    logic [3:0] temp0, temp1, temp2;
    always_ff @(posedge clk) begin
        if (start) begin
            temp0 <= $urandom_range(0, 15);
            temp1 <= temp0 + 4'd3;
            temp2 <= temp1 ^ 4'hF;
            done  <= temp2[0];
        end
    end
endmodule
