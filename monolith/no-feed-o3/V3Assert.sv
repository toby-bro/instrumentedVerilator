module immediate_assertion (
    input  logic [3:0] x,
    output logic       y
);
    always_comb begin
        assert (x < 4'hF);
        y = x[0];
    end
endmodule
module concurrent_properties (
    input  logic clk,
    input  logic rst_n,
    input  logic a,
    input  logic b,
    output logic y
);
    property p_seq;
        @(posedge clk) disable iff (!rst_n) a ##1 b;
    endproperty
    property p_assume;
        @(posedge clk) disable iff (!rst_n) a |-> b;
    endproperty
    property p_restrict;
        @(posedge clk) disable iff (!rst_n) b |-> a;
    endproperty
    assert  property (p_seq);
    assume  property (p_assume);
    cover   property (p_seq);
    restrict property (p_restrict);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) y <= 1'b0;
        else        y <= a ^ b;
    end
endmodule
module unique_if_example (
    input  logic [1:0] sel,
    input  logic [7:0] a,
    input  logic [7:0] b,
    input  logic [7:0] c,
    output logic [7:0] y
);
    always_comb begin
        unique if (sel == 2'b00) y = a;
        else if (sel == 2'b01)   y = b;
        else                     y = c;
    end
endmodule
module case_variants (
    input  logic [1:0] sel,
    input  logic [7:0] d0,
    input  logic [7:0] d1,
    input  logic [7:0] d2,
    output logic [7:0] y
);
    priority case (sel)
        2'b00:   y = d0;
        2'b01:   y = d1;
        default: y = d2;
    endcase
endmodule
module past_and_sampled (
    input  logic clk,
    input  logic rst_n,
    input  logic dat,
    output logic past_sig
);
    property p_past;
        @(posedge clk) disable iff (!rst_n) dat |-> $past(dat);
    endproperty
    property p_sampled;
        @(posedge clk) disable iff (!rst_n) $sampled(dat) |-> dat;
    endproperty
    assert property (p_past);
    cover  property (p_sampled);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) past_sig <= 1'b0;
        else        past_sig <= dat;
    end
endmodule
module assertion_control_tasks (
    input  logic clk,
    input  logic en,
    output logic state
);
    always_ff @(posedge clk) begin
        if (en) begin
            $asserton;
        end else begin
            $assertoff;
            $monitoroff(1);
        end
        state <= en;
    end
endmodule
