module overlap_write (
    input  logic [7:0] in_upper,
    input  logic [7:0] in_lower,
    output logic [15:0] out_sig
);
    logic [15:0] sig;
    always_comb begin
        sig[15:8] = in_upper;   
        sig[7:0]  = in_lower;   
        out_sig   = sig;
    end
endmodule
module dpi_pure_mod (
    input  int in_val,
    output int out_val
);
    import "DPI-C" pure function int pure_func (input int x); 
    always_comb begin
        out_val = pure_func(in_val); 
    end
endmodule
module dpi_unpure_mod (
    input  int in_val,
    output int out_val
);
    import "DPI-C" function int unpure_func (input int x); 
    always_comb begin
        out_val = unpure_func(in_val); 
    end
endmodule
module comb_loop_mod (
    input  logic in_sig,
    output logic loop_out
);
    wire a, b;
    assign a       = ~b;          
    assign b       =  in_sig ^ a;
    assign loop_out = a & b;
endmodule
module large_assign_mod (
    input  logic [31:0] din,
    output logic [31:0] dout
);
    logic [31:0] regs [0:99];     
    integer i;
    always_comb begin
        regs[0] = din;
        for (i = 1; i < 100; i++) begin
            regs[i] = regs[i-1] + i; 
        end
        dout = regs[99];
    end
endmodule
