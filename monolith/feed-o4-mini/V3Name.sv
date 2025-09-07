class SimpleClass;
    function new();
    endfunction
    function logic method(input logic x);
        method = ~x;
    endfunction
endclass
module mod_var(input logic clk, input logic d, output logic q);
    logic temp;
    assign temp = d;
    assign q = temp;
endmodule
module mod_varref(input logic [3:0] a, output logic [3:0] b);
    logic [3:0] internal;
    assign internal = a;
    assign b = internal + 1;
endmodule
module mod_cfunc(input logic [7:0] in_val, output logic [7:0] out_val);
    function logic [7:0] incr(input logic [7:0] v);
        incr = v + 1;
    endfunction
    assign out_val = incr(in_val);
endmodule
module mod_cell(input logic clk, input logic d, output logic q);
    mod_var ivar(.clk(clk), .d(d), .q(q));
endmodule
module mod_uorstruct(input logic [7:0] din, output logic [3:0] dout);
    typedef union packed {
        logic [7:0] full;
        struct packed { logic [3:0] hi; logic [3:0] lo; } parts;
    } u_t;
    u_t u;
    assign u.full = din;
    assign dout = u.parts.lo;
endmodule
module mod_member_dtype(input logic [3:0] in_s, output logic [1:0] out_s);
    typedef struct packed {
        logic [1:0] f1;
        logic [1:0] f2;
    } s_t;
    s_t s;
    always_comb begin
        s.f1 = in_s[1:0];
        s.f2 = in_s[3:2];
        out_s = s.f1;
    end
endmodule
module mod_member_sel(input logic [7:0] in_union, output logic [3:0] out);
    typedef union packed {
        logic [7:0] u8;
        struct packed { logic [3:0] a; logic [3:0] b; } parts;
    } u2_t;
    u2_t u2;
    assign u2.u8 = in_union;
    assign out = u2.parts.b;
endmodule
module mod_struct_sel(input logic [1:0] idx, input logic val, output logic out);
    typedef struct { logic a; logic b; } st_t;
    st_t st_arr [2];
    always_comb begin
        st_arr[0].a = val;
        st_arr[1].b = ~val;
        out = st_arr[idx].b;
    end
endmodule
module mod_scope(input logic in_s, output logic out_s);
    genvar gi;
    generate
        for (gi = 0; gi < 1; gi = gi + 1) begin : named_scope
            logic a;
            assign a = in_s;
            assign out_s = a;
        end
    endgenerate
endmodule
module mod_node(input logic a, output logic b);
    assign b = a;
endmodule
module mod_class_inst(input logic a, output logic b);
    always_comb begin
        SimpleClass sc = new();
        b = sc.method(a);
    end
endmodule
