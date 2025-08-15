interface my_iface;
    logic req;
    logic gnt;
endinterface
package my_types_pkg;
    typedef struct packed {
        logic [31:0]  a;
        logic [127:0] big;
    } my_struct_t;
    typedef union packed {
        logic [159:0] u160;
        my_struct_t   s;
    } my_union_t;
endpackage
package my_classes_pkg;
    class base_c;
        logic [63:0] small;
        function new(logic [63:0] s);
            small = s;
        endfunction
    endclass
    class derived_c extends base_c;
        logic [511:0] wide;
        function new(logic [63:0] s, logic [511:0] w);
            super.new(s);
            wide = w;
        endfunction
    endclass
endpackage
module class_user_mod (
    input  logic [7:0]   in_data,
    output logic [511:0] out_data
);
    import my_classes_pkg::*;
    always_comb begin
        automatic derived_c d = new({56'd0, in_data}, {504'd0, in_data});
        out_data = d.wide;
    end
endmodule
module struct_user_mod (
    input  logic [31:0]   in_a,
    input  logic [127:0]  in_big,
    output logic [127:0]  out_big
);
    import my_types_pkg::*;
    always_comb begin
        automatic my_struct_t s;
        s.a   = in_a;
        s.big = in_big;
        out_big = s.big;
    end
endmodule
module iface_user_mod (
    my_iface            inf,
    input  logic        data_in,
    output logic        data_out
);
    assign data_out = data_in ^ inf.req;
endmodule
module union_user_mod (
    input  logic         sel,
    input  logic [159:0] data_in,
    output logic [31:0]  data_out
);
    import my_types_pkg::*;
    always_comb begin
        automatic my_union_t u;
        u.u160 = data_in;
        if (sel) begin
            data_out = u.u160[31:0];
        end else begin
            data_out = u.s.a;
        end
    end
endmodule
