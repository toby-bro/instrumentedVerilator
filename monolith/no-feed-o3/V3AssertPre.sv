module m_prop_call (
    input  logic clk,
    input  logic a,
    output logic out
);
    default clocking cb @(posedge clk); endclocking
    property inner_p (input logic sig);
        @(posedge clk) $rose(sig);
    endproperty
    property outer_p (input logic sig2);
        inner_p(sig2);
    endproperty
    assert property (outer_p(a));
    assign out = a;
endmodule
module m_cycle_delay (
    input  logic clk,
    input  logic rst_n,
    input  logic a,
    input  logic b,
    output logic done
);
    default clocking dck @(posedge clk);
        input a, b, rst_n;
    endclocking
    sequence seq_a_b;
        a ##1 b;
    endsequence
    property p_delay;
        disable iff (!rst_n)
        seq_a_b;
    endproperty
    assert property (p_delay);
    assign done = a & b;
endmodule
module m_clocking_io (
    input  logic clk,
    input  logic in1,
    output logic cv_out
);
    logic driver;
    logic temp;
    clocking cb @(posedge clk);
        input  #2 in1;          
        output cv_out = driver; 
    endclocking
    default clocking cb;        
    always_ff @(posedge clk)
        driver <= in1;
    always_ff @(posedge clk)
        temp <= cb.cv_out;
endmodule
module m_stable_rose_fell (
    input  logic clk,
    input  logic sig,
    output logic flag
);
    assert property (@(posedge clk) $rose(sig)  |-> !sig);
    assert property (@(posedge clk) $fell(sig)  |->  sig);
    assert property (@(posedge clk) $stable(sig)|-> (sig == $past(sig)));
    assign flag = sig;
endmodule
module m_default_disable (
    input  logic clk,
    input  logic rst_n,
    input  logic data_in,
    output logic data_out
);
    default disable iff (!rst_n);
    default clocking clk_blk @(posedge clk); input data_in; endclocking
    assert property (data_in);
    assign data_out = data_in;
endmodule
module m_clockvar_write (
    input  logic clk,
    input  logic din,
    output logic dout
);
    clocking cb @(posedge clk);
        output dout = din;
    endclocking
    always_ff @(posedge clk)
        dout <= din;
endmodule
