typedef struct packed {
    logic [3:0] a;
    logic [7:0] b;
} struct12_t;
module unary_cast_mod(
    input  logic signed [7:0] in_data,
    output logic        [31:0] out_data
);
    always_comb begin
        out_data = +(~in_data);
    end
endmodule
module binary_ops_mod(
    input  logic signed   [31:0] a,
    input  logic unsigned [31:0] b,
    output logic signed   [63:0] y
);
    always_comb begin
        y = (a + b)
          - (a - b)
          + (a * b)
          + (a / (b | 32'd1))
          + (a % (b | 32'd1))
          + (a <  b)
          + (a <= b)
          + (a >  b)
          + (a >= b);
    end
endmodule
module cond_class_mod(
    input  logic sel,
    output logic [31:0] out_val
);
    class Base;
        virtual function int foo(); return 0; endfunction
    endclass
    class Deriv1 extends Base;
        function int foo(); return 11; endfunction
    endclass
    class Deriv2 extends Base;
        function int foo(); return 22; endfunction
    endclass
    Base tmp;
    always_comb begin
        automatic Deriv1 d1 = new();
        automatic Deriv2 d2 = new();
        tmp     = sel ? d1 : d2;
        out_val = tmp.foo();
    end
endmodule
module struct_pack_mod(
    input  logic [11:0] bus_in,
    output struct12_t   bus_out
);
    always_comb begin
        bus_out = '{a: bus_in[3:0], b: bus_in[11:4]};
    end
endmodule
module shift_cast_mod(
    input  logic  [7:0] in_x,
    input  logic  [4:0] shift_amt,
    output logic [63:0] out_q
);
    always_comb begin
        out_q = ({56'd0, in_x} << shift_amt);
    end
endmodule
module wide_const_mod(
    input  logic dummy,
    output logic [127:0] out_wide
);
    always_comb begin
        out_wide = 128'hFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF;
    end
endmodule
module negate_compare_mod(
    input  logic [15:0] lhs,
    input  logic [15:0] rhs,
    output logic [31:0] result
);
    always_comb begin
        result = -(lhs < rhs);
    end
endmodule
module var_ref_cast_mod(
    input  logic [1:0]  bits,
    output logic [63:0] value
);
    always_comb begin
        automatic logic [7:0] small_local;
        small_local = {6'b0, bits};
        value = (small_local << 30);
    end
endmodule
