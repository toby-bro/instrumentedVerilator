module implicit_event_mod (
    input  logic in_sig,
    output logic out_sig
);
    always_comb begin
        out_sig = ~in_sig;
    end
endmodule
module explicit_event_list_mod (
    input  logic clk_a,
    input  logic clk_b,
    output logic toggled
);
    always @(posedge clk_a or negedge clk_b) begin
        toggled <= clk_a ^ clk_b;
    end
endmodule
module edge_event_ff_mod (
    input  logic clk,
    input  logic d,
    output logic q
);
    always_ff @(posedge clk) begin
        q <= d;
    end
endmodule
module property_sequence_mod (
    input  logic clk,
    input  logic a,
    input  logic b,
    input  logic c,
    input  logic en,
    output logic dummy
);
    sequence seq_a;
        @(posedge clk) a;
    endsequence
    sequence seq_b;
        @(posedge clk) b;
    endsequence
    sequence seq_or;
        seq_a or seq_b;
    endsequence
    sequence seq_delay;
        seq_a ##2 seq_b;
    endsequence
    property prop_main;
        @(posedge clk iff en) seq_or |-> ##1 c;
    endproperty
    assert property (prop_main);
    assign dummy = c;
endmodule
module repeated_event_task_mod (
    input  logic clk,
    input  logic start,
    output logic done
);
    task automatic wait_cycles (input int n, input logic clk_i);
        repeat (n) @(posedge clk_i);
    endtask
    always_ff @(posedge clk) begin
        if (start)
            wait_cycles(3, clk);
    end
    assign done = start;
endmodule
