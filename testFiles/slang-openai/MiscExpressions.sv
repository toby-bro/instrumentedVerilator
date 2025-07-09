package mypkg;
    parameter int PKG_PARAM = 42;
endpackage
module min_typ_max_mod(
    input  logic [7:0] in1,
    output logic [7:0] out1
);
    parameter int PSEL = (1:2:3);
    assign out1 = in1 + PSEL;
endmodule
module dist_constraint_mod(
    input  logic clk,
    output logic [7:0] rv_o
);
    class dist_c;
        rand bit [7:0] rv;
        constraint c_dist { rv dist { 8'hAA :/ 1, 8'h55 :/ 2, [8'h10 : 8'h20] :/ 3 }; }
    endclass
    always_comb begin
        automatic dist_c c = new;
        void'(c.randomize());
        rv_o = c.rv;
    end
endmodule
module tagged_union_mod(
    input  logic dummy,
    output logic [31:0] out_union
);
    typedef union tagged {
        int   ai;
        real  ar;
    } tag_u_t;
    tag_u_t myu;
    always_comb begin
        myu = tagged ai 32'd123;
        out_union = myu.ai;
    end
endmodule
module copy_class_mod(
    input  logic dummy,
    output logic done
);
    class base_c;
        int data;
        function base_c copy();
            base_c tmp = new;
            tmp.data = data;
            return tmp;
        endfunction
    endclass
    always_comb begin
        automatic base_c obj1 = new;
        automatic base_c obj2;
        obj1.data = 5;
        obj2 = obj1.copy();
        done = (obj2.data == obj1.data);
    end
endmodule
module assertion_mod(
    input  logic clk,
    input  logic rst,
    output logic out_ok
);
    logic a, b;
    assign a = clk;
    assign b = ~clk;
    sequence seq1(int x, int y);
        x ##1 y;
    endsequence
    property prop1(int p);
        @(posedge clk) seq1(p, p);
    endproperty
    let eq_let(int l, int r) = (l == r);
    assert property(prop1(a));
    cover  property(prop1(b));
    logic res;
    assign res = eq_let(1, 1);
    assign out_ok = res;
endmodule
module pkg_ref_mod(
    input  logic [3:0] in_data,
    output logic [7:0] out_data
);
    import mypkg::*;
    assign out_data = in_data + PKG_PARAM;
endmodule
module clocking_mod(
    input  logic clk,
    output logic sampled_out
);
    logic data;
    clocking cb @(posedge clk);
        input data;
    endclocking
    assign sampled_out = cb.data;
endmodule
