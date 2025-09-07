module lifetime_mod
    (input  logic         clk,
     input  logic  [7:0]  din,
     output logic  [7:0]  dout);
    function automatic logic [7:0] accumulate (input logic [7:0] val);
        static logic [7:0] acc = 8'h0;
        acc = acc + val;
        return acc;
    endfunction
    always_ff @(posedge clk) begin
        dout <= accumulate(din);
    end
endmodule
module typedef_mod
    (input  logic  [1:0] sel,
     output logic        flag);
    typedef enum logic [1:0] {
        ST0 = 2'b00,
        ST1 = 2'b01,
        ST2 = 2'b10,
        ST3 = 2'b11
    } state_e;
    typedef struct packed {
        logic [7:0] data;
        logic       parity;
    } pkt_t;
    state_e state_var;
    always_comb begin
        state_var = state_e'(sel);
        flag      = (state_var == ST2);
    end
endmodule
module generate_mod
    #(parameter int WIDTH = 4)
    (input  logic [WIDTH-1:0] in_bus,
     output logic [WIDTH-1:0] out_bus);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : genblk_loop
            assign out_bus[i] = in_bus[WIDTH-1-i];
        end
        if (WIDTH == 0) begin : genblk_zero
        end
    endgenerate
endmodule
module foreach_mod
    (input  logic [7:0] in_vec,
     output logic [7:0] out_vec);
    logic [7:0] tmp;
    always_comb begin
        tmp = '0;
        foreach (in_vec[idx]) begin
            tmp[idx] = in_vec[7-idx];
        end
        out_vec = tmp;
    end
endmodule
module attribute_mod
    (input  logic a_in,
     output logic b_out);
    (* keep = "true" *) logic [3:0] sig /* verilator public_flat_rw */;
    always_comb begin
        sig   = {4{a_in}};
        b_out = sig[0];
    end
endmodule
module clocking_mod
    (input  logic clk,
     input  logic rst_n,
     output logic q);
    logic d;
    clocking cb @(posedge clk);
        input  d;
        output q;
    endclocking
    always_comb d = ~rst_n;
    always_ff @(posedge clk) begin
        cb.q <= cb.d;
    end
endmodule
module class_mod
    (input  logic in_sig,
     output logic out_sig);
    class simple_c;
        int val;
        function new(int v = 0);
            val = v;
        endfunction
        function int get();
            return val;
        endfunction
    endclass
    simple_c obj = null;
    always_comb begin
        if (obj == null)
            obj = new(5);          
        out_sig = in_sig & obj.get()[0];
    end
endmodule
module paramtype_mod
    #(parameter type T = logic,
      parameter int  W = 8)
    (input  T in_t,
     output T out_t);
    assign out_t = in_t;
endmodule
