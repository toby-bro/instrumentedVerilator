package mypkg;
    typedef struct packed {logic [31:0] data;} mystruct_t;
endpackage
module cast_width_mod #(parameter W = 5) (
    input  logic [W-1:0] in1,
    output logic [W-1:0] out1
);
    logic signed [W:0] tmp_signed;
    logic        [W:0] tmp_unsigned;
    always_comb begin
        tmp_signed   = $signed({1'b0, in1});
        tmp_unsigned = $unsigned(tmp_signed);
        out1 = byte'(tmp_unsigned) ^ int'(in1);
    end
endmodule
module param_type_mod #(parameter type T = logic [7:0]) (
    input  T in_t,
    output T out_t
);
    always_comb begin
        out_t = T'(in_t);
    end
endmodule
module enum_mod (
    input  logic [1:0] sel,
    output logic       done
);
    typedef enum logic [1:0] {S0 = 2'd0, S1 = 2'd1, S2 = 2'd2} state_e;
    state_e state;
    always_comb begin
        state = state_e'(sel);
        done  = (state == S2);
    end
endmodule
module struct_mod (
    input  logic [15:0] in16,
    output logic [7:0]  out8
);
    typedef struct packed {
        logic [7:0] lo;
        logic [7:0] hi;
    } two_byte_t;
    two_byte_t sb;
    always_comb begin
        sb   = two_byte_t'(in16);
        out8 = sb.lo ^ sb.hi;
    end
endmodule
module union_mod (
    input  logic [15:0] in_u,
    output logic [7:0]  out_u
);
    typedef union packed {
        logic [15:0] whole;
        struct packed {
            logic [7:0] lo;
            logic [7:0] hi;
        } parts;
    } u16_t;
    u16_t u;
    always_comb begin
        u      = u16_t'(in_u);
        out_u  = u.parts.lo | u.parts.hi;
    end
endmodule
module class_extend_mod (
    input  logic in0,
    output logic out0
);
    class base_c;
        function void f(); endfunction
    endclass
    class derived_c extends base_c;
        function void f(); super.f(); endfunction
    endclass
    derived_c d;
    always_comb begin
        d = new();
        out0 = in0;
    end
endmodule
module virtual_class_mod (
    input  logic a,
    output logic b
);
    virtual class interface_c;
        pure virtual function bit op(bit inp);
    endclass
    class impl_c extends interface_c;
        function bit op(bit inp);
            return ~inp;
        endfunction
    endclass
    impl_c inst;
    always_comb begin
        inst = new();
        b = inst.op(a);
    end
endmodule
module pure_constraint_mod (
    input  logic [7:0] dummy_in,
    output logic       done
);
    virtual class abstract_c;
        rand bit [7:0] value;
        pure constraint keep_value;
    endclass
    class concrete_c extends abstract_c;
        constraint keep_value { value == dummy_in; }
    endclass
    concrete_c c;
    always_comb begin
        c = new();
        done = 1'b0;
    end
endmodule
module arg_default_mod (
    input  logic [7:0] in_val,
    output logic [7:0] out_val
);
    function automatic logic [7:0] identity(input logic [7:0] val = 8'hAA);
        return val;
    endfunction
    assign out_val = identity(in_val);
endmodule
module package_ref_mod (
    input  logic [31:0] in_data,
    output logic [31:0] out_data
);
    import mypkg::*;
    mystruct_t s;
    always_comb begin
        s.data  = in_data;
        out_data = s.data;
    end
endmodule
module local_prot_mod (
    input  logic [31:0] in_data,
    output logic [31:0] out_data
);
    class Outer;
        local int secret;
        function new(int v);
            secret = v;
        endfunction
        class Inner;
            function int getSecret(Outer o);
                return o.secret;
            endfunction
        endclass
    endclass
    always_comb begin
        Outer o_local = new(in_data);
        Outer::Inner inner_local = new();
        out_data = inner_local.getSecret(o_local);
    end
endmodule
