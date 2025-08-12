module lifetime_demo(input logic clk, output logic [7:0] out);
    const int CONST_VAL = 8;
    logic [7:0] out_reg;
    always_ff @(posedge clk) begin : proc
        automatic int auto_counter = 0;
        static   int static_accum  = CONST_VAL;
        auto_counter = auto_counter + 1;
        static_accum = static_accum + auto_counter;
        out_reg      <= static_accum[7:0];
    end
    assign out = out_reg;
endmodule
module net_demo(input logic in0, output wire out0);
    wire scalared [3:0] vect_net;
    wand wand_net;
    wire (strong1, weak0) strength_net = 1'b0;
    assign vect_net = {4{in0}};
    assign wand_net = &vect_net;
    assign out0 = strength_net;
endmodule
module function_demo(input logic [7:0] a_in, output logic [7:0] result);
    function automatic int add(ref int a, const ref int b, input int c);
        a = a + b + c;
        return a;
    endfunction
    always_comb begin
        int v1 = a_in;
        const int v2 = 5;
        result = add(v1, v2, 3);
    end
endmodule
module foreach_demo(input logic clk, output logic [7:0] sum_out);
    logic [7:0] arr [0:3];
    logic [7:0] total;
    always_ff @(posedge clk) begin
        foreach (arr[i])
            arr[i] <= i;
        total <= 0;
        foreach (arr[idx])
            total <= total + arr[idx];
    end
    assign sum_out = total;
endmodule
module clocking_demo(input logic clk, input logic data_in, output logic data_out);
    logic internal;
    clocking cb @(posedge clk);
        input  in_sig  = data_in;
        output out_sig = internal;
    endclocking
    always_ff @(posedge clk)
        internal <= cb.in_sig;
    assign data_out = internal;
endmodule
module assertion_demo(input logic clk, input logic d, output logic pass);
    property p_local;
        @(posedge clk) $rose(d) |-> d;
    endproperty
    assert property (p_local);
    assign pass = 1'b1;
endmodule
