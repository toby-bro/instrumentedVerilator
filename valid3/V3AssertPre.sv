module implication_mod (
    input  logic clk,
    input  logic rst_n,
    input  logic a,
    input  logic b,
    output logic y
);
    assign y = a & b;
    property p_implication;
        @(posedge clk) disable iff (!rst_n) a |=> b;
    endproperty
    assert property (p_implication);
    property p_stable_y;
        @(posedge clk) disable iff (!rst_n) $stable(y);
    endproperty
    cover property (p_stable_y);
    property p_past_a;
        @(posedge clk) disable iff (!rst_n) (a && !$past(a));
    endproperty
    assert property (p_past_a);
endmodule
module default_disable_mod (
    input  logic clk,
    input  logic rst_n,
    input  logic x,
    input  logic z_in,
    output logic z_out
);
    assign z_out = z_in;
    default disable iff (!rst_n);
    property p_overlap;
        @(posedge clk) x |-> z_in;
    endproperty
    assert property (p_overlap);
endmodule
module edge_detect_mod (
    input  logic clk,
    input  logic sig,
    output logic edge_seen
);
    always_ff @(posedge clk) edge_seen <= sig;
    property p_rose_sig;
        @(posedge clk) $rose(sig);
    endproperty
    property p_fell_sig;
        @(posedge clk) $fell(sig);
    endproperty
    property p_stable_sig;
        @(posedge clk) $stable(sig);
    endproperty
    assert property (p_rose_sig);
    cover  property (p_fell_sig);
    cover  property (p_stable_sig);
endmodule
module struct_member_mod (
    input  logic clk,
    input  logic sel,
    output logic out_sig
);
    typedef struct packed {
        logic a;
        logic b;
    } pair_t;
    pair_t s;
    assign out_sig = s.a & s.b;
    always_ff @(posedge clk) begin
        if (sel) begin
            s.a <= ~s.a;
            s.b <=  sel;
        end
    end
    property p_member_rose;
        @(posedge clk) $rose(s.a);
    endproperty
    assert property (p_member_rose);
endmodule
