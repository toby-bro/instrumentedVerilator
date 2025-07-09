module prop_class_mod(
    input  logic in_sig,
    output logic out_sig
);
    class PropClass;
        rand  bit randbit;
        randc bit randcbit;
        local bit local_bit;
        protected int prot_int;
        static const int CONSTVAL = 32;
        static int static_int;
        function new();
            this.randbit  = 0;
            this.randcbit = 1;
        endfunction
        function int get_prot();
            return prot_int;
        endfunction
    endclass
    PropClass pc;
    initial begin
        pc = new();
        void'(pc.randomize());
    end
    assign out_sig = in_sig;
endmodule
module inheritance_mod(
    input  logic in_sig,
    output logic out_sig
);
    virtual class Base;
        int a;
        virtual function void func(); endfunction
        function new(int aa = 0);
            a = aa;
        endfunction
    endclass
    class Derived extends Base;
        int b;
        function new();
            super.new(5);
            b = 1;
        endfunction
        function void func();
            a = a + b;
        endfunction
    endclass
    Derived d;
    initial begin
        d = new();
        d.func();
    end
    assign out_sig = in_sig;
endmodule
module interface_impl_mod(
    input  logic in_sig,
    output logic out_sig
);
    interface class Iface;
        pure virtual function int calc(int a);
    endclass
    class Impl implements Iface;
        virtual function int calc(int a);
            return a * 2;
        endfunction
    endclass
    Impl obj;
    int  result;
    initial begin
        obj    = new();
        result = obj.calc(3);
    end
    assign out_sig = in_sig;
endmodule
module constraint_mod(
    input  logic in_sig,
    output logic out_sig
);
    class WithConstraint;
        rand int value;
        constraint range_c  { value inside {[0:15]}; }
        static constraint static_c { value >= 0; }
        extern constraint even_c;
    endclass
    constraint WithConstraint::even_c { value % 2 == 0; }
    WithConstraint wc;
    initial begin
        wc = new();
        void'(wc.randomize());
    end
    assign out_sig = in_sig;
endmodule
module generic_class_mod(
    input  logic in_sig,
    output logic out_sig
);
    class Generic #(
        type       T = int,
        parameter  int N = 1
    );
        T arr [N];
        function new();
            foreach (arr[idx]) arr[idx] = '0;
        endfunction
        function T get(int idx);
            return arr[idx];
        endfunction
    endclass
    Generic#(bit, 4) g;
    bit tmp;
    initial begin
        g   = new();
        tmp = g.get(0);
    end
    assign out_sig = in_sig;
endmodule
module randmode_mod(
    input  logic in_sig,
    output logic out_sig
);
    class RClass;
        rand bit data;
        function new(); endfunction
        function void enable_rand(bit on_ff);
            rand_mode(on_ff);
        endfunction
    endclass
    RClass rc;
    initial begin
        rc = new();
        rc.enable_rand(1'b1);
    end
    assign out_sig = in_sig;
endmodule
