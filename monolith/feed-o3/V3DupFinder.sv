module mod_dumpLevel #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic [WIDTH-1:0] y
);
    wire [WIDTH-1:0] tmp1 = a & b;
    wire [WIDTH-1:0] tmp2 = a & b;   
    assign y = tmp1 | tmp2;
endmodule
module mod_debug (
    input  logic [3:0] in_val,
    output logic [3:0] out_val
);
    logic [3:0] w1, w2;
    always_comb begin
        w1 = in_val + 4'd1;
    end
    always_comb begin
        w2 = in_val + 4'd1;  
    end
    assign out_val = w1 ^ w2;
endmodule
module mod_erase (
    input  logic  [7:0] a,
    input  logic  [7:0] b,
    output logic  [8:0] y
);
    function automatic int mult1 (input int x, input int y);
        mult1 = x * y;
    endfunction
    function automatic int mult2 (input int x, input int y);
        mult2 = x * y;   
    endfunction
    wire [8:0] res1 = mult1(a, b);
    wire [8:0] res2 = mult2(a, b);
    assign y = res1 + res2;
endmodule
module mod_findDuplicate (
    input  logic [1:0] state_in,
    output logic [1:0] state_out
);
    typedef enum logic [1:0] {
        S_IDLE  = 2'd0,
        S_BUSY  = 2'd1,
        S_DONE  = 2'd2
    } state_e;
    typedef enum logic [1:0] {
        S_IDLE_D  = 2'd0,
        S_BUSY_D  = 2'd1,
        S_DONE_D  = 2'd2
    } state_e_dup;   
    always_comb begin
        case (state_in)
            S_IDLE  : state_out = state_e'(S_IDLE_D);
            S_BUSY  : state_out = state_e'(S_BUSY_D);
            default : state_out = state_e'(S_DONE_D);
        endcase
    end
endmodule
module mod_dumpFile #(parameter WIDTH = 4) (
    input  logic [WIDTH-1:0] a,
    output logic [WIDTH-1:0] y
);
    generate
        genvar i;
        for (i = 0; i < WIDTH; i++) begin : g
            logic t1, t2;
            always_comb begin
                t1 = a[i];
            end
            always_comb begin
                t2 = a[i];   
            end
            assign y[i] = t1 | t2;
        end
    endgenerate
endmodule
module mod_dumpFilePrefixed #(parameter USE = 1, parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);
    wire [WIDTH-1:0] w1;
    wire [WIDTH-1:0] w2;
    generate
        if (USE) begin : blk1
            assign w1 = data_in;
        end
        if (USE) begin : blk2
            assign w2 = data_in;  
        end
    endgenerate
    assign data_out = w1 & w2;
endmodule
module dup_modA (
    input  logic in_sig,
    output logic out_sig
);
    assign out_sig = in_sig & in_sig;
endmodule
module dup_modB (
    input  logic in_sig,
    output logic out_sig
);
    assign out_sig = in_sig & in_sig;  
endmodule
