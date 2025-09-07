module cnew_example (
    input  logic clk,
    input  logic rst_n,
    output logic [7:0] data_out
);
    class my_packet;
        rand bit [7:0] payload;
        function new();
            payload = 8'hAA;
        endfunction
    endclass
    my_packet pkt;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            pkt      = new;          
            data_out <= pkt.payload;
        end
        else if (pkt.randomize()) begin
            data_out <= pkt.payload; 
        end
    end
endmodule
module dumpctl_example (
    input  logic in_sig,
    output logic out_sig
);
    assign out_sig = in_sig;
    initial begin
        $dumpfile("dumpctl_example.vcd");
        $dumpvars(0, dumpctl_example);
        $dumpon;
    end
endmodule
module dist_biop_example (
    input  logic clk,
    output logic [3:0] dist_val
);
    class rand_gen;
        rand bit [3:0] v;
        constraint dist_c { v dist { [0:1] :/ 10, [2:3] :/ 20 }; } 
    endclass
    rand_gen rg;
    always_ff @(posedge clk) begin
        if (rg == null) rg = new;
        if (rg.randomize()) dist_val <= rg.v;
    end
endmodule
module dist_triop_example (
    input  logic clk,
    output logic [7:0] dist_val
);
    class rand_gen2;
        rand bit [7:0] v;
        constraint dist_c {
            v dist {
                8'hAA := 1,                 
                8'h55 :/ 2,                 
                [8'h00:8'h0F] := 5          
            };
        }
    endclass
    rand_gen2 rg2;
    always_ff @(posedge clk) begin
        if (rg2 == null) rg2 = new;
        if (rg2.randomize()) dist_val <= rg2.v;
    end
endmodule
