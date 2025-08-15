module child_unit #(parameter WIDTH = 8)(
    input  logic [WIDTH-1:0] in_c,
    output logic [WIDTH-1:0] out_c
);
    assign out_c = in_c;
endmodule
module cell_parent(
    input  logic [7:0] in_p,
    output logic [7:0] out_p
);
    logic [7:0] internal_wire;
    child_unit #(.WIDTH(8)) u_child (
        .in_c  (in_p),
        .out_c (internal_wire)
    );
    assign out_p = internal_wire;
endmodule
module basic_var_mod(
    input  logic        clk,
    input  logic [7:0]  in_b,
    output logic [7:0]  out_b
);
    logic [7:0] reg_data;
    (* verilator public *) logic [7:0] pub_data;
    always_comb begin
        reg_data = in_b;
        pub_data = reg_data;
        out_b    = pub_data;
    end
endmodule
module func_mod(
    input  logic [31:0] in_a,
    output logic [31:0] out_a
);
    function automatic logic [31:0] sv_add(input logic [31:0] x, input logic [31:0] y);
        sv_add = x + y;
    endfunction
    always_comb begin
        out_a = sv_add(in_a, 32'd10);
    end
endmodule
module struct_mod(
    input  logic [3:0] in_s,
    output logic [7:0] out_s
);
    typedef struct packed {
        logic [3:0] get;
        logic [3:0] set;
    } s_t;
    s_t my_struct;
    always_comb begin
        my_struct.get = in_s;
        my_struct.set = ~in_s;
        out_s = {my_struct.get, my_struct.set};
    end
endmodule
