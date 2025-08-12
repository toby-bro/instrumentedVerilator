module prop_features(
    input  logic clk,
    output logic [7:0] out_data
);
    class PropClass;
        rand  bit [7:0] rand_var;
        randc bit [3:0] randc_var;
        static const int CONST_DATA = 32;
        protected bit [7:0] pdat;
        local    static bit [7:0] ls_data;
        function new(bit [7:0] init = 0);
            pdat = init;
        endfunction
    endclass
    always_ff @(posedge clk) begin
        automatic PropClass obj = new();
        void'(obj.randomize());
        out_data <= obj.rand_var;
    end
endmodule
module inheritance_features(
    input  logic clk,
    input  logic rst,
    output logic [31:0] count_out
);
    virtual class Base;
        rand int value;
        pure virtual function void inc();
        bit [31:0] counter;
        function new(int start = 0);
            counter = start;
        endfunction
    endclass
    class Derived extends Base;
        function new();
            super.new(5);
        endfunction
        virtual function void inc();
            counter++;
        endfunction
    endclass
    always_ff @(posedge clk) begin
        if (rst)
            count_out <= 32'd0;
        else begin
            automatic Derived d = new();
            d.inc();
            count_out <= d.counter;
        end
    end
endmodule
module generic_features #(parameter int W = 16)(
    input  logic in_sig,
    output logic [W-1:0] out_sig
);
    class GenClass #(parameter int WIDTH = 8, type PT = int);
        PT data;
        function void set(PT d); data = d; endfunction
        function PT  get(); return data; endfunction
    endclass
    always_comb begin
        automatic GenClass #(.WIDTH(W), .PT(logic [W-1:0])) obj = new();
        obj.set({W{in_sig}});
        out_sig = obj.get();
    end
endmodule
module constraint_features(
    input  logic clk,
    output logic done
);
    class Constr;
        rand bit [7:0] b;
        constraint c_block { b inside {[0:99]}; }
        constraint base_c  { b < 90; }
        constraint child_c { b > 10; }
        function void post_randomize(); endfunction
    endclass
    always_ff @(posedge clk) begin
        automatic Constr c = new();
        void'(c.randomize());
        done <= 1'b1;
    end
endmodule
module interface_features(
    input  logic clk,
    output logic [7:0] q
);
    interface class Iface;
        pure virtual function int get();
    endclass
    class Impl implements Iface;
        int v;
        function new(int g = 0); v = g; endfunction
        virtual function int get(); return v; endfunction
    endclass
    always_ff @(posedge clk) begin
        automatic Impl im = new(123);
        q <= im.get();
    end
endmodule
module external_constraint_feature(
    input  logic clk,
    output logic flag
);
    class ConWithPrototype;
        rand bit [3:0] y;
        extern constraint c_proto;
    endclass
    constraint ConWithPrototype::c_proto { y inside {[1:15]}; }
    always_ff @(posedge clk) begin
        automatic ConWithPrototype obj = new();
        void'(obj.randomize());
        flag <= &obj.y;
    end
endmodule
