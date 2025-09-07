interface bus_if;
    logic       clk;
    logic [7:0] data;
    modport master (input clk, output data);
endinterface
module quadop_partsel(
    input  logic [15:0] in_data,
    output logic [7:0]  out_data
);
    assign out_data = in_data[4 +: 8];
endmodule
module class_new_ex(
    input  logic [3:0] in_val,
    output logic [3:0] out_val
);
    class Foo;
        bit [3:0] val;
        function new(); val = 0; endfunction
    endclass
    always_comb begin
        Foo f;
        f = new();
        f.val = in_val;
        out_val = f.val;
    end
endmodule
module sformatf_mod(
    input  logic [7:0] in_byte,
    output logic [7:0] out_byte
);
    string s;
    always_comb begin
        s = $sformatf("BYTE=%0d", in_byte);
        out_byte = in_byte;
    end
endmodule
module queue_with_mod(
    input  logic [31:0] in_val,
    output logic        hit
);
    function automatic int has_val(input int v);
        int q[$];
        int i;
        q.push_back(v);
        for (i = 0; i < q.size(); i++) begin
            if (q[i] == v) return 1;
        end
        return 0;
    endfunction
    always_comb begin
        hit = has_val(in_val);
    end
endmodule
module ucfunc_mod(
    input  logic [31:0] in_word,
    output logic [31:0] out_word
);
    import "DPI-C" pure function int add_one(input int a);
    import "DPI-C" function void do_nothing(input int a);
    always_comb begin
        do_nothing(in_word);
    end
    assign out_word = add_one(in_word);
endmodule
module intf_ref_mod(
    input  logic             dummy_in,
    output logic [7:0]       out_data,
    virtual bus_if.master    vif
);
    always_comb begin
        out_data = vif.data;
    end
endmodule
package mypkg;
    typedef enum logic [1:0] {IDLE, RUN, STOP} state_t;
    parameter logic [3:0] CONST_VAL = 4'ha;
endpackage
module scope_typedef_mod#
   (parameter type T = logic [3:0])(
    input  logic [3:0]    val_in,
    output mypkg::state_t state_out,
    output logic [3:0]    const_out
);
    import mypkg::*;
    typedef T local_t;
    assign state_out = RUN;
    assign const_out = CONST_VAL;
endmodule
module cons_pack_mod(
    input  logic       s_in,
    output logic [2:0] s_out
);
    typedef struct packed {logic a; logic [2:0] b;} st_t;
    st_t st_fixed = '{default:0};
    st_t st2;
    always_comb begin
        st2 = '{a: s_in, b: 3'h0};
        s_out = st2.b | st_fixed.b;
    end
endmodule
