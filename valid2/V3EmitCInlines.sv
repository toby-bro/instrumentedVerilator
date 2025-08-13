module dynamic_new_example (
    input  logic [31:0] in_data,
    output logic [31:0] out_data
);
    class Packet;
        logic [31:0] data;
        function new(input logic [31:0] d);
            data = d;
        endfunction
    endclass
    always_comb begin
        Packet p = new(in_data);   
        out_data = p.data;
    end
endmodule
module dump_control_example (
    input  logic  sig_in,
    output logic  sig_out
);
    initial begin
        $dumpfile("dump_control_example.vcd");
        $dumpvars(0, dump_control_example);
    end
    assign sig_out = sig_in;
endmodule
module dist_biop_example (
    input  logic       dummy_in,
    output logic [7:0] random_out
);
    class RandBiop;
        rand bit [7:0] val;
        constraint c { val dist { [0:3] := 1, 4 := 2 }; }
    endclass
    logic [7:0] tmp;
    initial begin
        RandBiop rb = new();
        void'(rb.randomize());
        tmp = rb.val;
    end
    assign random_out = tmp ^ {8{dummy_in}};
endmodule
module dist_triop_example (
    input  logic       sel_in,
    output logic [7:0] rand_out
);
    class RandTriop;
        rand bit [7:0] v;
        constraint c { v dist { [0:5] :/ 2, 6 :/ 1 }; }
    endclass
    logic [7:0] tmp2;
    initial begin
        RandTriop rt = new();
        void'(rt.randomize());
        tmp2 = rt.v;
    end
    assign rand_out = sel_in ? tmp2 : 8'h00;
endmodule
