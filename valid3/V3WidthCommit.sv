module m_signed_ops (
    input  logic signed [15:0] in_a,
    input  logic        [15:0] in_b,
    output logic        [31:0] out_y
);
    assign out_y = $signed(in_a) + $unsigned(in_b) + int'(in_a) + longint'(in_b);
endmodule
module m_struct_enum (
    input  logic [3:0] sel,
    output logic [7:0] out_v
);
    typedef enum logic [1:0] {
        ST_IDLE = 2'd0,
        ST_RUN  = 2'd1,
        ST_STOP = 2'd2
    } state_e;
    typedef struct packed {
        logic [3:0] idx;
        logic       flag;
    } my_s_t;
    my_s_t s_reg;
    always_comb begin
        s_reg.idx  = sel;
        s_reg.flag = (state_e'(sel[1:0]) == ST_RUN);
        out_v      = {s_reg.idx, s_reg.flag};
    end
endmodule
module m_union_type (
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
    typedef union packed {
        logic [7:0]                   whole;
        struct packed { logic [3:0] lo; logic [3:0] hi; } split;
    } u_t;
    u_t u_reg;
    always_comb begin
        u_reg.whole = in_data;
        out_data    = {u_reg.split.hi, u_reg.split.lo};
    end
endmodule
module m_param #(
    type T = logic [7:0]
) (
    input  T in_p,
    output T out_p
);
    function automatic T id (input T d = '0);
        id = d;
    endfunction
    assign out_p = id(in_p);
endmodule
module m_class_features (
    input  logic [7:0] in_val,
    output logic [7:0] out_val
);
    class Base;
        virtual function int process (input int v = 0);
            process = v + 1;
        endfunction
    endclass
    class Derived extends Base;
        protected int offset;
        local     int internal_v;
        function new ();
            offset      = 5;
            internal_v  = 2;
        endfunction
        virtual function int process (input int v = 0);
            process = super.process(v) + offset + internal_v;
        endfunction
    endclass
    Base    base_h;
    Derived der_h;
    always_comb begin
        base_h = new();
        der_h  = new();
        out_val = der_h.process(in_val);
    end
endmodule
module m_virtual_constraint (
    input  logic dummy_in,
    output logic dummy_out
);
    virtual class AbstractC;
        rand bit [7:0] rv;
        pure constraint c0;
        pure virtual function void doit ();
    endclass
    class ConcreteC extends AbstractC;
        constraint c0 { rv < 8'd200; }
        function void doit (); endfunction
        constraint val_c { rv >= 8'd0; }
    endclass
    AbstractC abs_h;
    ConcreteC con_h;
    always_comb begin
        con_h = new();
        abs_h = con_h;
        dummy_out = dummy_in;
    end
endmodule
