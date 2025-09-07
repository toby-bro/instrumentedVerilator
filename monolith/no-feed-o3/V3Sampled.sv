module sampled_prop1 (
    input  logic clk,
    input  logic req,
    input  logic ack,
    output logic ready
);
    sequence s_req_to_ack;
        req ##1 ack;
    endsequence
    property p_req2ack;
        @(posedge clk) s_req_to_ack;
    endproperty
    assert property (p_req2ack);
    assign ready = ack;
endmodule
module clocking_sampled2 (
    input  logic        clk,
    input  logic [7:0]  d_in,
    output logic [7:0]  d_out
);
    clocking cb @(posedge clk);
        input  d_in;
        output d_out;
    endclocking
    always_comb cb.d_out = cb.d_in;
    sequence s_stable;
        cb.d_in ##1 cb.d_in;
    endsequence
    property p_stable;
        @(posedge clk) s_stable;
    endproperty
    assert property (p_stable);
endmodule
module sampled_past3 (
    input  logic        clk,
    input  logic [3:0]  din,
    output logic        diff_not_zero
);
    property p_change;
        @(posedge clk) ($past(din) != din) |-> diff_not_zero;
    endproperty
    assert property (p_change);
    always_ff @(posedge clk)
        diff_not_zero <= (din != 4'd0);
endmodule
module sampled_cover4 (
    input  logic        clk,
    input  logic [3:0]  a,
    output logic [3:0]  y
);
    covergroup cg @(posedge clk);
        coverpoint a;
    endgroup
    cg cg_inst;
    initial begin
        cg_inst = new();
    end
    assign y = a;
endmodule
module sampled_class5 (
    input  logic clk,
    input  logic start,
    output logic done
);
    class simpleClass;
        bit flag;
        function void toggle();
            flag = ~flag;
        endfunction
    endclass
    simpleClass sc;
    always_ff @(posedge clk) begin
        if (sc == null) sc = new();
        if (start) sc.toggle();
        done <= sc.flag;
    end
endmodule
