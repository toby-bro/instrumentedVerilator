module sformat_mod #(parameter SIZE = 8) (
    input  logic [SIZE-1:0] data_in,
    output logic [SIZE-1:0] data_out
);
    string str_a;
    string str_b;
    always_comb begin
        str_a = $sformatf("VAL=%0d", data_in);
        str_b = $psprintf("PSVAL=%0d", data_in);
        data_out = data_in;
    end
endmodule
module plusargs_mod #(parameter WIDTH = 32) (
    input  logic [WIDTH-1:0] in_val,
    output logic [WIDTH-1:0] out_val
);
    integer arg_val;
    logic   plusargs_found;
    always_comb begin
        arg_val = 0;
        plusargs_found = $value$plusargs("PLUS_ARG=%d", arg_val);
        out_val = in_val ^ arg_val;
    end
endmodule
module scope_randomize_mod (
    input  logic clk,
    input  logic trigger,
    output logic [15:0] rand_val
);
    logic [15:0] tmp;
    function automatic void do_rand (ref logic [15:0] v);
        void'(randomize(v));
    endfunction
    always_ff @(posedge clk) begin
        if (trigger)
            do_rand(tmp);
        rand_val <= tmp;
    end
endmodule
module class_randomize_mod (
    input  logic clk,
    output logic [7:0] rand_out
);
    class mycls;
        rand logic [7:0] val;
    endclass
    mycls obj;
    always_ff @(posedge clk) begin
        if (obj == null)
            obj = new();
        if (obj.randomize())
            rand_out <= obj.val;
    end
endmodule
module global_clock_mod (
    input  logic clk_in,
    input  logic d,
    output logic q
);
    always @($global_clock) begin
        q <= d;
    end
endmodule
module inferred_mod (
    input  logic in_sig,
    output logic out_sig
);
    sequence inferred_seq (event clk_ev = $inferred_clock);
        in_sig ##1 in_sig;
    endsequence
    property inferred_prop (logic dis_sig = $inferred_disable);
        inferred_seq |-> !dis_sig;
    endproperty
    assign out_sig = in_sig;
endmodule
module seqmethod_mod (
    input  logic in_sig,
    output logic match_out
);
    sequence seq1;
        in_sig ##1 in_sig;
    endsequence
    property seq_status;
        seq1.triggered or seq1.matched;
    endproperty
    assign match_out = in_sig;
endmodule
