class dummy_class;
    function void foo(); endfunction
endclass
module clocking_demo (
    input  logic clk,
    input  logic in_sig,
    output logic out_sig
);
    clocking cb @(posedge clk);
        default input #0 output #0;
        input  in_sig;
        output out_sig;
    endclocking
    default clocking cb;
    always_ff @(cb) begin
        cb.out_sig <= cb.in_sig;
    end
    always_comb begin
        static dummy_class d = new();
        d.foo();
    end
endmodule
module assert_disable_demo (
    input  logic clk,
    input  logic rst_n,
    input  logic a,
    input  logic b,
    output logic y
);
    clocking cb @(posedge clk);
        input  a;
        input  b;
    endclocking
    default clocking cb;
    default disable iff (!rst_n);
    property p_dis;
        @(posedge clk) disable iff (!rst_n) a |-> b;
    endproperty
    assert property (p_dis);
    assign y = a & b;
    always_comb begin
        static dummy_class d = new();
        d.foo();
    end
endmodule
module property_call_demo (
    input  logic clk,
    input  logic p,
    input  logic q,
    output logic r
);
    clocking cb @(posedge clk);
        input p;
        input q;
    endclocking
    default clocking cb;
    property base_prop (logic x, logic y);
        @(posedge clk) x |=> y;
    endproperty
    property wrapper_prop (logic u, logic v);
        base_prop(u, v);
    endproperty
    assert property (wrapper_prop(p, q));
    assign r = p ^ q;
    always_comb begin
        static dummy_class d = new();
        d.foo();
    end
endmodule
module edge_demo (
    input  logic clk,
    input  logic a,
    input  logic b,
    output logic c
);
    clocking cb @(posedge clk);
        input  a;
        input  b;
        output c;
    endclocking
    default clocking cb;
    property edge_prop;
        @(posedge clk) $rose(a) |-> $fell(b);
    endproperty
    cover property (edge_prop);
    always_ff @(cb) begin
        cb.c <= a & b;
    end
    always_comb begin
        static dummy_class d = new();
        d.foo();
    end
endmodule
module cycle_delay_assign_mod (
    input  logic clk,
    input  logic d_in,
    output logic d_out
);
    clocking cb @(posedge clk);
        default input #0 output #0;
        input  d_in;
        output d_out;
    endclocking
    default clocking cb;
    always_ff @(cb) begin
        cb.d_out <= ##1 cb.d_in;
    end
    always_comb begin
        static dummy_class d = new();
        d.foo();
    end
endmodule
module stable_past_mod (
    input  logic clk,
    input  logic s,
    input  logic t,
    output logic u
);
    clocking cb @(posedge clk);
        input  s;
        input  t;
        output u;
    endclocking
    default clocking cb;
    property stable_prop;
        @(posedge clk) $stable(s) |-> ##1 t;
    endproperty
    assert property (stable_prop);
    property past_prop;
        @(posedge clk) $past(s) |=> u;
    endproperty
    cover property (past_prop);
    always_ff @(cb) begin
        cb.u <= s & t;
    end
    always_comb begin
        static dummy_class d = new();
        d.foo();
    end
endmodule
