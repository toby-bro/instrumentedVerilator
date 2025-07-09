`timescale 1ns/1ps
module mod_basic_seq(
    input  logic clk,
    input  logic rst_n,
    input  logic a,
    input  logic b,
    output logic y
);
    assign y = a & b;
    sequence seq_basic;
        a ##1 b[*2:4];
    endsequence
    property prop_basic;
        @(posedge clk) disable iff (!rst_n) seq_basic |=> b;
    endproperty
    assert property (prop_basic);
endmodule
module mod_concat(
    input  logic clk,
    input  logic a,
    input  logic b,
    input  logic c,
    input  logic d,
    output logic z
);
    assign z = c | d;
    sequence s1; a; endsequence
    sequence s2; b[*0:$]; endsequence
    sequence seq_concat;
        s1 ##[1:3] s2 ##0 (c ##2 d);
    endsequence
    assert property ( @(posedge clk) strong(seq_concat) );
endmodule
module mod_binary_seq(
    input  logic clk,
    input  logic a,
    input  logic b,
    input  logic c,
    output logic o
);
    assign o = a ^ b;
    sequence sa; a; endsequence
    sequence sb; b; endsequence
    sequence sc; c; endsequence
    sequence s_or;     sa or sb;        endsequence
    sequence s_and;    sa and sb;       endsequence
    sequence s_int;    sa intersect sb; endsequence
    sequence s_thr;    a throughout sc; endsequence
    sequence s_within; sa within sc;    endsequence
    assert property ( @(posedge clk) s_thr |-> o );
endmodule
module mod_unary_prop(
    input  logic clk,
    input  logic a,
    input  logic b,
    output logic o
);
    assign o = a;
    sequence s_ev; a ##1 b; endsequence
    property p_always;
        @(posedge clk) always     [2:4] s_ev |-> b;
    endproperty
    property p_eventually;
        @(posedge clk) eventually [1:3] s_ev;
    endproperty
    assert property (p_always);
    assert property (not p_eventually);
endmodule
module mod_first_match(
    input  logic clk,
    input  logic a,
    input  logic b,
    output logic o
);
    assign o = b;
    sequence s_fm;
        first_match( a ##[1:2] b );
    endsequence
    assert property ( @(posedge clk) s_fm |=> o );
endmodule
module mod_parent_seq(
    input  logic clk,
    input  logic a,
    input  logic b,
    input  logic c,
    output logic y
);
    assign y = c;
    sequence s_inner; a ##1 b; endsequence
    property p_rep;
        @(posedge clk) (s_inner)[*2] |-> c;
    endproperty
    assert property (p_rep);
endmodule
module mod_strong_weak_abort(
    input  logic clk,
    input  logic a,
    input  logic b,
    input  logic c,
    output logic o
);
    assign o = c;
    sequence s_sw; a ##1 b; endsequence
    property p_strong; strong(s_sw); endproperty
    property p_weak;   weak  (s_sw); endproperty
    assert property ( @(posedge clk)  accept_on (c)       p_strong );
    assert property ( @(posedge clk)  sync_reject_on (!c) p_weak   );
endmodule
module mod_cond_case(
    input  logic clk,
    input  logic a,
    input  logic b,
    input  logic c,
    input  logic [1:0] sel,
    output logic o
);
    assign o = sel[0];
    property p_if;
        if (a) (b |-> c) else (c |-> b);
    endproperty
    property p_case;
        case (sel)
            2'b00: a |-> b;
            2'b01, 2'b10: b |-> c;
            default: c |-> a;
        endcase
    endproperty
    assert property ( @(posedge clk) p_if  );
    assert property ( @(posedge clk) p_case);
endmodule
module mod_disable_iff(
    input  logic clk,
    input  logic rst,
    input  logic a,
    input  logic b,
    output logic o
);
    assign o = a & ~b;
    assert property ( @(posedge clk) disable iff (rst) (a |-> b) );
endmodule
module mod_clocking(
    input  logic clk,
    input  logic a,
    input  logic b,
    output logic o
);
    assign o = a | b;
    clocking cb @(posedge clk);
    endclocking
    property p_clk;
        @cb a |=> b;
    endproperty
    assert property (p_clk);
endmodule
