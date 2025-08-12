module signal_event_module (
    input  logic clk,
    input  logic rst_n,
    input  logic in,
    output logic out
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            out <= 1'b0;
        else
            out <= in;
    end
endmodule
module iff_event_module (
    input  logic clk,
    input  logic enable,
    input  logic din,
    output logic dout
);
    always @(posedge clk iff enable) begin
        dout <= din;
    end
endmodule
module implicit_event_module (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] y
);
    always @* begin
        y = a + b;
    end
endmodule
module repeated_event_module (
    input  logic        clk,
    input  logic [3:0]  cnt_in,
    input  logic        val_in,
    output logic        val_out
);
    always begin
        repeat (cnt_in) @(posedge clk);
        val_out = val_in;
    end
endmodule
module cycle_delay_module (
    input  logic clk,
    input  logic in,
    output logic out
);
    clocking cb @(posedge clk);
        input  in;
        output out;
    endclocking
    default clocking cb;
    always begin
        ##2;
        out <= in;
    end
endmodule
module property_sequence_module (
    input  logic clk,
    input  logic a,
    input  logic b,
    output logic o
);
    sequence seq_ab;
        @(posedge clk) a ##1 b;
    endsequence
    property prop_seq_ab;
        seq_ab;
    endproperty
    assert property (prop_seq_ab);
    assign o = a & b;
endmodule
