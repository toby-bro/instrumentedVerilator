typedef struct packed {
    logic a;
    logic b;
} my_s;
module assert_clocking_example (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [7:0]  din,
    output logic [7:0]  dout
);
    logic [7:0] internal_reg;
    default disable iff (!rst_n);
    clocking cb @(posedge clk);
        input  din;
        output dout;
    endclocking
    default clocking cb;
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            internal_reg <= '0;
            dout         <= '0;
        end else begin
            internal_reg <= din;
            dout         <= internal_reg;
        end
    end
    property p1;
        @(posedge clk) disable iff (!rst_n) din |-> ##1 dout;
    endproperty
    assert property (p1);
endmodule
module property_call_example (
    input  logic clk,
    input  logic en,
    input  logic a,
    input  logic b,
    output logic y
);
    default disable iff (!en);
    property p_child (logic arg1, logic arg2);
        arg1 |-> ##1 arg2;
    endproperty
    property p_parent (logic p, logic q);
        disable iff (!en)
        p_child(p, q);
    endproperty
    assert property (@(posedge clk) p_parent(a, b));
    assign y = a & b;
endmodule
module edge_check_example (
    input  logic clk,
    input  logic rst_n,
    input  logic sig,
    output logic ok
);
    default disable iff (!rst_n);
    property fell_p;
        @(posedge clk) $fell(sig);
    endproperty
    property rose_p;
        @(posedge clk) $rose(sig);
    endproperty
    property stable_p;
        @(posedge clk) $stable(sig);
    endproperty
    cover property (fell_p);
    cover property (rose_p);
    cover property (stable_p);
    assign ok = sig;
endmodule
module past_implication_example (
    input  logic clk,
    input  logic rst_n,
    input  logic in1,
    input  logic in2,
    output logic out1
);
    default disable iff (!rst_n);
    property past_imp;
        @(posedge clk) ($past(in1) && !in1) |-> in2;
    endproperty
    assert property (past_imp);
    assign out1 = in1 ^ in2;
endmodule
module struct_member_example (
    input  logic clk,
    input  logic rst_n,
    input  logic din_a,
    input  logic din_b,
    output logic dout_b
);
    default disable iff (!rst_n);
    my_s s;
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            s <= '0;
        end else begin
            s.a <= din_a;
            s.b <= din_b;
        end
    end
    assign dout_b = s.b;
    property member_prop;
        @(posedge clk) $rose(s.a) |-> s.b;
    endproperty
    assert property (member_prop);
endmodule
