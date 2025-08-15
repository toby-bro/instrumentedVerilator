module dynamic_new_m #(parameter WIDTH = 8) (
    input  logic                 clk,
    input  logic                 rst_n,
    input  logic [WIDTH-1:0]     in_data,
    output logic [WIDTH-1:0]     out_data
);
    class Packet;
        bit [WIDTH-1:0] data;
        function new;
            data = '0;
        endfunction
        function void set_data(bit [WIDTH-1:0] d);
            data = d;
        endfunction
        function bit [WIDTH-1:0] get_data;
            return data;
        endfunction
    endclass
    Packet pkt;
    always @(posedge clk) begin
        if (!rst_n)
            pkt = null;
        else if (pkt == null)
            pkt = new;
    end
    always_comb begin
        if (pkt == null) begin
            out_data = '0;
        end else begin
            pkt.set_data(in_data);
            out_data = pkt.get_data();
        end
    end
endmodule
module dump_ctl_m (
    input  logic clk,
    input  logic din,
    output logic q
);
    always_ff @(posedge clk)
        q <= din;
endmodule
module randcase_m #(parameter W = 4) (
    input  logic         clk,
    input  logic         trigger,
    output logic [W-1:0] out_val
);
    logic [W-1:0] temp;
    always @(posedge clk) begin
        if (trigger) begin
            randcase
                1: temp <= '0;
                1: temp <= {W{1'b1}};
            endcase
        end
    end
    assign out_val = temp;
endmodule
module dist_constraint_m #(parameter W = 8) (
    input  logic             clk,
    input  logic             start,
    output logic [W-1:0]     val
);
    class RandGen;
        rand bit [W-1:0] num;
        constraint num_c {
            num dist { [0:50]  := 1,
                       [51:255] := 3 };
        }
    endclass
    RandGen rg;
    always @(posedge clk) begin
        if (rg == null)
            rg = new;
        if (start && rg.randomize())
            val <= rg.num;
    end
endmodule
module simple_m (
    input  logic in_sig,
    output logic out_sig
);
    assign out_sig = ~in_sig;
endmodule
