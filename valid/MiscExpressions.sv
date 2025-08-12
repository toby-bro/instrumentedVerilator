module auto_var_mod(
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
    function automatic logic [7:0] incr(input logic [7:0] a);
        automatic logic [7:0] b;
        b = a + 8'd1;
        return b;
    endfunction
    always_comb begin
        out_data = incr(in_data);
    end
endmodule
module min_typ_max_mod #(
    parameter int P_WIDTH = 4:8:16
) (
    input  logic [P_WIDTH-1:0] dat_in,
    output logic [P_WIDTH-1:0] dat_out
);
    assign dat_out = dat_in;
endmodule
module dist_expr_mod(
    input  logic [31:0] add_in,
    output logic [31:0] add_out
);
    class dist_c;
        rand int value;
        constraint c { value dist {1 := 2, [2:4] :/ 3, 5 := 1}; }
    endclass
    always_comb begin
        automatic dist_c rc = new();
        add_out = rc.value + add_in;
    end
endmodule
module tagged_union_mod(
    input  logic [7:0] in_byte,
    output logic [7:0] out_byte
);
    typedef union tagged {
        struct { logic [7:0] data; } DATA;
        void                 NONE;
    } my_tagged_t;
    my_tagged_t u;
    always_comb begin
        u = tagged DATA'{data: in_byte};
        out_byte = u.DATA.data;
    end
endmodule
module type_ref_mod(
    input  logic [7:0] dummy_in,
    output logic [31:0] bits_out
);
    typedef logic [15:0] half_word_t;
    assign bits_out = $bits(half_word_t);
endmodule
module hierarchical_mod(
    input  logic sig_in,
    output logic sig_out
);
    generate
        if (1) begin : blk
            logic internal_sig;
        end
    endgenerate
    always_comb begin
        blk.internal_sig = sig_in;
    end
    assign sig_out = blk.internal_sig;
endmodule
module copyclass_mod(
    input  logic [31:0] in_val,
    output logic [31:0] out_val
);
    class base_c;
        int data;
        function base_c copy();
            base_c tmp = new();
            tmp.data = data;
            return tmp;
        endfunction
    endclass
    always_comb begin
        automatic base_c c1 = new();
        automatic base_c c2;
        c1.data = in_val;
        c2 = c1.copy();
        out_val = c2.data;
    end
endmodule
