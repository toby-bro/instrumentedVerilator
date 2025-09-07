module random_basic_mod
    (input  logic [7:0] in_data,
     output logic [7:0] out_data);
    class basic_c;
        rand bit [7:0] a;
        constraint c1 { a inside { [0:200] }; }
    endclass
    basic_c obj;
    always_comb begin
        obj = new();
        void'(obj.randomize());
        out_data = obj.a ^ in_data;
    end
endmodule
module random_inline_mod
    (input  logic [3:0] din,
     output logic [3:0] dout);
    class inline_c;
        rand bit [3:0] a;
    endclass
    inline_c o;
    always_comb begin
        o = new();
        void'(o.randomize() with { a inside { 1,2,3 }; });
        dout = o.a ^ din;
    end
endmodule
module rand_mode_mod
    (input  logic clk,
     output logic [7:0] x_out);
    class rand_c;
        rand bit [7:0] x;
    endclass
    rand_c ob;
    always_ff @(posedge clk) begin
        ob = new();
        ob.x.rand_mode(0);
        void'(ob.randomize());
        x_out <= ob.x;
    end
endmodule
module constraint_mode_mod
    (input  logic clk,
     output logic [4:0] y_out);
    class cm_c;
        rand bit [4:0] y;
        constraint c_y { y > 2; }
    endclass
    cm_c co;
    always_ff @(posedge clk) begin
        co = new();
        co.constraint_mode(0);
        void'(co.randomize());
        y_out <= co.y;
    end
endmodule
module std_random_mod
    (input  logic dummy,
     output logic [7:0] out1,
     output logic [7:0] out2);
    bit [7:0] a;
    bit [7:0] b;
    always_comb begin
        void'(std::randomize(a, b) with { a < b; });
        out1 = a;
        out2 = b;
    end
endmodule
module randcase_mod
    (input  logic dummy_sel,
     output logic out_sel);
    always_comb begin
        randcase
            10: out_sel = 1'b0;
            20: out_sel = 1'b1;
        endcase
    end
endmodule
module rand_arrays_mod
    (input  logic dummy,
     output logic [7:0] out);
    class arr_c;
        rand bit [7:0] da[];          
        rand bit [7:0] qa[$];         
        constraint size_c { da.size() inside {[1:4]}; }
        constraint each_c { foreach (da[i]) da[i] inside { [0:50] }; }
    endclass
    arr_c o;
    always_comb begin
        o = new();
        void'(o.randomize());
        if (o.da.size() > 0)
            out = o.da[0];
        else
            out = 8'h00;
    end
endmodule
module rand_enum_mod
    (input  logic dummy,
     output logic [1:0] col_out);
    typedef enum logic [1:0] {RED=0, GREEN=1, BLUE=2} colors_e;
    class color_c;
        randc colors_e col;
    endclass
    color_c cobj;
    always_comb begin
        cobj = new();
        void'(cobj.randomize());
        col_out = cobj.col;
    end
endmodule
