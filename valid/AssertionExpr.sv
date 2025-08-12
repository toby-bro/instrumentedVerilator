module m_simple_seq (
    input  logic clk,
    input  logic rst_n,
    input  logic a,
    input  logic b,
    output logic y
);
    sequence s_basic;
        a ##1 b;
    endsequence
    property p_basic;
        @(posedge clk) disable iff (!rst_n) s_basic[*2];
    endproperty
    assert property (p_basic);
    assign y = a & b;
endmodule
module m_binary_ops (
    input  logic clk,
    input  logic a,
    input  logic b,
    input  logic c,
    input  logic d,
    output logic y
);
    sequence sA;
        a ##[1:3] b;
    endsequence
    sequence sB;
        c ##1 d;
    endsequence
    property p_or;         @(posedge clk)   sA or  sB;        endproperty
    property p_and;        @(posedge clk)   sA and sB;        endproperty
    property p_intersect;  @(posedge clk)   sA intersect sB;  endproperty
    property p_within;     @(posedge clk)   sA within sB;     endproperty
    property p_throughout; @(posedge clk)   a throughout sB;  endproperty
    assert property (p_or);
    assert property (p_and);
    assert property (p_intersect);
    assert property (p_within);
    assert property (p_throughout);
    assign y = a ^ b ^ c ^ d;
endmodule
module m_unary_ops (
    input  logic clk,
    input  logic sig,
    output logic y
);
    sequence s_un;
        sig;
    endsequence
    property p_not;        @(posedge clk) not      s_un;             endproperty
    property p_always;     @(posedge clk) always   s_un;             endproperty
    property p_eventually; @(posedge clk) eventually [1:3] s_un;     endproperty
    assert property (p_not);
    assert property (p_always);
    assert property (p_eventually);
    assign y = sig;
endmodule
module m_strong_weak (
    input  logic clk,
    input  logic p,
    input  logic q,
    output logic z
);
    sequence s_sw;
        p ##1 q;
    endsequence
    assert property ( @(posedge clk) strong(s_sw) );
    assert property ( @(posedge clk) weak  (s_sw) );
    assign z = p & q;
endmodule
module m_abort (
    input  logic clk,
    input  logic enable,
    input  logic data,
    output logic z
);
    sequence s_acc;
        data;
    endsequence
    assert property ( @(posedge clk) accept_on (enable)  s_acc );
    assert property ( @(posedge clk) reject_on (!enable) s_acc );
    assign z = data & enable;
endmodule
module m_conditional_prop (
    input  logic clk,
    input  logic sel,
    input  logic x,
    input  logic y_in,
    output logic y_out
);
    sequence s_x;  x;     endsequence
    sequence s_y;  y_in;  endsequence
    property p_cond;
        @(posedge clk) if (sel) s_x else s_y;
    endproperty
    assert property (p_cond);
    assign y_out = sel ? x : y_in;
endmodule
module m_case_prop (
    input  logic clk,
    input  logic [1:0] sel,
    input  logic a,
    input  logic b,
    output logic outp
);
    sequence s0; a; endsequence
    sequence s1; b; endsequence
    property p_case;
        @(posedge clk)
        case (sel)
            2'd0: s0;
            2'd1: s1;
            default: s0 or s1;
        endcase
    endproperty
    assert property (p_case);
    assign outp = (sel == 2'd0) ? a :
                  (sel == 2'd1) ? b : (a | b);
endmodule
module m_disable_iff (
    input  logic clk,
    input  logic rst_n,
    input  logic in_sig,
    output logic out_sig
);
    property p_dis;
        @(posedge clk) disable iff (!rst_n) in_sig;
    endproperty
    assert property (p_dis);
    assign out_sig = rst_n & in_sig;
endmodule
module m_clocking_assert (
    input  logic clk,
    input  logic d,
    output logic q
);
    clocking cb @(posedge clk);
        input d;
    endclocking
    sequence s_clk;
        cb.d;
    endsequence
    assert property ( @(cb) s_clk );
    assign q = d;
endmodule
module m_first_match (
    input  logic clk,
    input  logic rst_n,
    input  logic a,
    input  logic b,
    input  logic c,
    output logic result
);
    sequence s_long;
        a ##[1:3] b;
    endsequence
    property p_first;
        @(posedge clk) disable iff (!rst_n) first_match (s_long);
    endproperty
    assert property (p_first);
    assign result = a & b & c;
endmodule
