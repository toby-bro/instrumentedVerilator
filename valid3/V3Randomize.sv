module rand_basic_mod (
    input  logic [7:0] inp,
    output logic [7:0] outp
);
    class RB_Class;
        rand bit [7:0] a;
        rand bit [7:0] b;
        constraint c_range { a inside {[0:255]}; b < a; }
        function void pre_randomize();
            a.rand_mode(1);
        endfunction
        function void post_randomize();
            a.rand_mode(0);
        endfunction
    endclass
    always_comb begin
        RB_Class obj = new();
        void'(obj.randomize());
        outp = inp ^ obj.a;
    end
endmodule
module rand_inline_mod (
    input  logic [3:0] sel_in_mod,
    output logic [7:0] d_out
);
    class RI_Class;
        rand bit [7:0] value;
    endclass
    always_comb begin
        RI_Class ri = new();
        bit ok;
        ok = ri.randomize() with { value == {4'h0, sel_in_mod}; };
        d_out = ri.value;
    end
endmodule
module rand_mode_mod (
    input  logic [7:0] vin,
    output logic [7:0] vout
);
    class RM_Class;
        rand bit [7:0] data;
        rand bit [7:0] keep;
        function void pre_randomize();
            data.rand_mode(0);
        endfunction
    endclass
    always_comb begin
        RM_Class rm = new();
        rm.keep.rand_mode(1);
        void'(rm.randomize());
        vout = vin + rm.keep;
    end
endmodule
module constraint_mode_mod (
    input  logic [7:0] seed,
    output logic [7:0] result
);
    class CM_Class;
        rand bit [7:0] num;
        constraint num_c { num < 8'h80; }
    endclass
    always_comb begin
        CM_Class cm = new();
        cm.num_c.constraint_mode(seed[0]);
        void'(cm.randomize());
        result = cm.num;
    end
endmodule
module randc_mod (
    input  logic clk_en,
    output logic [3:0] cyc_val
);
    class RC_Class;
        randc bit [3:0] cyc;
    endclass
    always_comb begin
        RC_Class rc = new();
        void'(rc.randomize());
        cyc_val = rc.cyc;
    end
endmodule
module dyn_array_mod (
    input  logic [3:0] idx,
    output logic [7:0] datum
);
    class DA_Class;
        rand bit [7:0] arr [];
        constraint c_vals { foreach (arr[i]) arr[i] inside {[0:255]}; }
    endclass
    always_comb begin
        DA_Class da = new();
        void'(da.randomize());
        datum = da.arr[idx & 2'd3];
    end
endmodule
module assoc_array_mod (
    input  logic [7:0] key,
    output logic [7:0] val
);
    class AA_Class;
        rand bit [7:0] aarr [string];
    endclass
    always_comb begin
        AA_Class aa = new();
        void'(aa.randomize());
        val = aa.aarr[$sformatf("%0d", key)];
    end
endmodule
module struct_mod (
    input  logic [3:0] sel_in_mod,
    output logic [7:0] struct_out
);
    typedef struct packed { bit [3:0] a; bit [3:0] b; } packed_s;
    class ST_Class;
        rand packed_s s;
    endclass
    always_comb begin
        ST_Class st = new();
        bit ok_struct;
        ok_struct = st.randomize() with { st.s.a == sel_in_mod; };
        struct_out = {st.s.a, st.s.b};
    end
endmodule
module randcase_mod (
    input  logic [3:0] inp,
    output logic [3:0] outp
);
    always_comb begin
        logic [3:0] tmp = 4'h0;
        randcase
            1: tmp = inp + 4'd1;
            1: tmp = inp - 4'd1;
        endcase
        outp = tmp;
    end
endmodule
