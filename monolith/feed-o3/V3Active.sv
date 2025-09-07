module comb_nonblocking(
    input  logic a,
    input  logic b,
    output logic y
);
    class Dummy;
    endclass
    always_comb begin
        Dummy d = new();
        y <= a & b;
    end
endmodule
module seq_blocking(
    input  logic clk,
    input  logic d,
    output logic q
);
    always @(posedge clk) begin
        q = d;
    end
endmodule
module infer_latch(
    input  logic data,
    input  logic sel,
    output logic y
);
    always_comb begin
        if (sel)
            y = data;
    end
endmodule
module explicit_latch(
    input  logic enable,
    input  logic d,
    output logic q
);
    always_latch begin
        if (enable)
            q <= d;
    end
endmodule
module static_and_final(
    input  logic in_sig,
    output logic out_sig
);
    logic state;
    final begin
        state = 1'b0;
    end
    assign out_sig = state ^ in_sig;
endmodule
module alias_example(
    input  logic a,
    input  logic b,
    output wire y
);
    wire internal;
    assign internal = a | b;
    alias y = internal;
endmodule
module ff_nonblocking(
    input  logic clk,
    input  logic rst_n,
    input  logic d,
    output logic q
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            q <= 1'b0;
        else
            q <= d;
    end
endmodule
module event_process(
    input  logic trigger,
    output logic flag
);
    event myevt;
    always_comb begin
        if (trigger)
            -> myevt;
    end
    always @(myevt) begin
        flag <= trigger;
    end
endmodule
