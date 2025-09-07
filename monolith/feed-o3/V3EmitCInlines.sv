module dynamic_new_mod (
    input  logic        clk,
    input  logic [7:0]  in_data,
    output logic [7:0]  out_data
);
    class packet;
        rand bit [7:0] data;
        function new(bit [7:0] d = 0);
            data = d;
        endfunction
    endclass
    always_ff @(posedge clk) begin
        packet p = new(in_data);   
        out_data <= p.data;
    end
endmodule
module dump_mod (
    input  logic trig,
    output logic out_sig
);
    initial begin
        $dumpfile("dump_mod.vcd");
        $dumpvars(0);
    end
    assign out_sig = trig;
endmodule
module randcase_mod (
    input  logic       clk,
    input  logic [3:0] seed,
    output logic [1:0] result
);
    logic [3:0] lfsr;
    always_ff @(posedge clk) begin
        lfsr <= {lfsr[2:0], seed[0] ^ lfsr[3]};
        randcase
            1: result <= 2'b00;
            1: result <= 2'b01;
            2: result <= 2'b10;
            3: result <= 2'b11;
        endcase
    end
endmodule
class rng_class;
    rand bit [3:0] val;
    constraint c_dist { val dist {4'h0 := 1, 4'h1 :/ 2, 4'hF := 3}; }
endclass
module dist_constraint_mod (
    input  logic       clk,
    input  logic       en,
    output logic [3:0] rnd
);
    rng_class r_inst;
    always_ff @(posedge clk) begin
        if (r_inst == null) r_inst = new; 
        if (en) begin
            void'(r_inst.randomize());   
            rnd <= r_inst.val;
        end
    end
endmodule
