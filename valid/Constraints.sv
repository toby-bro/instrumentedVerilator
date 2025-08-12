module expr_constraint_mod(input  logic [7:0] in_val,
                           output logic [7:0] out_val);
    class expr_cls;
        rand logic [7:0] a;
        rand logic [7:0] b;
        constraint expr_c {
            a inside { [8'd0 : 8'd10] };
            soft b == 8'd5;
            a dist { 8'd0 := 1, [8'd1 : 8'd5] := 4, 8'd10 := 1 };
        }
    endclass
    always_comb begin
        automatic expr_cls c = new();
        void'(c.randomize());
        out_val = in_val ^ c.a ^ c.b;
    end
endmodule
module implication_constraint_mod(input  logic [7:0] in_data,
                                  output logic [7:0] out_data);
    class impl_cls;
        rand logic [7:0] a;
        rand logic [7:0] b;
        constraint impl_c { (a > 8'd5) -> (b == a); }
    endclass
    always_comb begin
        automatic impl_cls c = new();
        void'(c.randomize());
        out_data = (in_data & c.a) | c.b;
    end
endmodule
module conditional_constraint_mod(input  logic [7:0] in_bus,
                                  output logic [7:0] out_bus);
    class cond_cls;
        rand logic [7:0] a;
        rand logic [7:0] b;
        constraint cond_c {
            if (a == 8'd0)  b == 8'd0;
            else            b inside { [8'd1 : 8'd15] };
        }
    endclass
    always_comb begin
        automatic cond_cls c = new();
        void'(c.randomize());
        out_bus = c.a + c.b + in_bus;
    end
endmodule
module uniqueness_constraint_mod(input  logic [7:0] data_in,
                                 output logic [7:0] data_out);
    typedef logic [7:0] byte_t;
    class uniq_cls;
        rand byte_t arr[3];
        constraint uniq_c { unique { arr[0], arr[1], arr[2] }; }
    endclass
    function automatic byte_t arr_xor(input byte_t a[3]);
        arr_xor = a[0] ^ a[1] ^ a[2];
    endfunction
    always_comb begin
        automatic uniq_cls c = new();
        void'(c.randomize());
        data_out = data_in ^ arr_xor(c.arr);
    end
endmodule
module disable_soft_constraint_mod(input  logic [3:0] in_sig,
                                   output logic [3:0] out_sig);
    class disable_soft_cls;
        rand logic [3:0] c;
        constraint soft_c     { soft c == 4'd7; }
        constraint disable_c  { disable soft c; }
    endclass
    always_comb begin
        automatic disable_soft_cls d = new();
        void'(d.randomize());
        out_sig = in_sig + d.c;
    end
endmodule
module solve_before_constraint_mod(input  logic [7:0] in_a,
                                   input  logic [7:0] in_b,
                                   output logic [7:0] out_z);
    class solve_cls;
        rand logic [7:0] a;
        rand logic [7:0] b;
        constraint order_c { solve a before b; }
        constraint limit_c {
            a inside { [8'd0 : 8'd20] };
            b inside { [8'd0 : 8'd20] };
        }
    endclass
    always_comb begin
        automatic solve_cls s = new();
        void'(s.randomize());
        out_z = (in_a + s.a) - (in_b + s.b);
    end
endmodule
module foreach_constraint_mod(input  logic        clk,
                              input  logic [7:0]  din,
                              output logic [7:0]  dout);
    typedef logic [7:0] byte_t;
    class foreach_cls;
        rand byte_t arr[4];
        constraint foreach_c { foreach (arr[i]) arr[i] inside { [8'd0 : 8'd15] }; }
    endclass
    always_ff @(posedge clk) begin
        automatic foreach_cls f = new();
        void'(f.randomize());
        dout <= din ^ f.arr[0];
    end
endmodule
module constraint_list_mod(input  logic [7:0] in_x,
                           output logic [7:0] out_y);
    class list_cls;
        rand logic [7:0] p;
        rand logic [7:0] q;
        rand logic [7:0] r;
        constraint blk {
            p inside { [8'd1 : 8'd10] };
            (q > 8'd5) -> (r == q);
            if (p == 8'd2) q == 8'd3; else q != 8'd0;
            r dist { 8'd0 := 1, 8'd1 := 2, 8'd2 := 3 };
            solve p before q;
        }
    endclass
    always_comb begin
        automatic list_cls l = new();
        void'(l.randomize());
        out_y = in_x + l.p + l.q + l.r;
    end
endmodule
