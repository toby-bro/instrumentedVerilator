//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
module rename_var_mod #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] in_data,
    output logic [WIDTH-1:0] out_data
);
    localparam int INTERNAL_CONST = 42;
    logic [WIDTH-1:0] data_reg;
    always_comb begin
        data_reg = in_data + INTERNAL_CONST[WIDTH-1:0];
    end
    assign out_data = in_data ^ data_reg;
endmodule
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
module struct_packed_mod (
    input  logic [3:0]  din,
    output logic [3:0]  dout
);
    typedef struct packed {
        bit [3:0] get;
        bit [3:0] set;
    } my_packed_t;
    my_packed_t s;
    always_comb begin
        s.get = din;
        s.set = ~din;
        dout  = s.get ^ s.set;
    end
endmodule
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
module union_packed_mod (
    input  logic  [7:0] data_in,
    output logic  [7:0] data_out
);
    typedef union packed {
        byte full;
        struct packed {
            bit [3:0] low;
            bit [3:0] high;
        } parts;
    } union_t;
    union_t u;
    always_comb begin
        u.full   = data_in;
        data_out = {u.parts.high, u.parts.low};
    end
endmodule
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
module dpi_mod (
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic [31:0] y
);
    import "DPI-C" function int dpi_add (input int aa, input int bb);
    always_comb begin
        y = dpi_add(a, b);
    end
endmodule
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
class simple_class;
    int value;
    function new(int v = 0); value = v; endfunction
    function void set(int v); value = v; endfunction
    function int get(); return value; endfunction
endclass
module class_holder_mod (
    input  logic  [7:0] in_val,
    output logic  [7:0] out_val
);
    simple_class c;
    always_comb begin
        if (c == null) c = new(0);
        c.set(in_val);
        out_val = c.get();
    end
endmodule
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
module child_mod #(parameter W = 4) (
    input  logic [W-1:0] in,
    output logic [W-1:0] out
);
    assign out = in + 1;
endmodule
module parent_mod (
    input  logic [3:0] a,
    output logic [3:0] y
);
    child_mod #(4) u_child (
        .in  (a),
        .out (y)
    );
endmodule
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
module struct_sel_mod (
    input  logic [7:0] vec_in,
    output logic       parity_out
);
    typedef struct packed {
        logic [3:0] nibble0;
        logic [3:0] nibble1;
    } nibbles_t;
    nibbles_t n;
    always_comb begin
        n.nibble0 = vec_in[3:0];
        n.nibble1 = vec_in[7:4];
        parity_out = ^n.nibble0 ^ ^n.nibble1;
    end
endmodule
