module width_mismatch_mod (
    input  logic [2:0] in_bus,
    output logic [3:0] out_bus
);
    assign out_bus = in_bus;
endmodule
module unused_signal_mod (
    input  logic  din,
    output logic  dout
);
    logic unused_wire;
    assign dout = din;
endmodule
module incomplete_case_mod (
    input  logic [1:0] sel,
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] y
);
    always_comb begin
        case (sel)
            2'b00: y = a;
            2'b01: y = b;
        endcase
    end
endmodule
module latch_inferred_mod (
    input  logic        en,
    input  logic [7:0]  d,
    output logic [7:0]  q
);
    logic [7:0] q_int;
    always_comb begin
        if (en) q_int = d;  
    end
    assign q = q_int;
endmodule
module constant_condition_mod (
    input  logic in_sig,
    output logic out_sig
);
    always_comb begin
        if (1'b0)                 
            out_sig = in_sig;
        else
            out_sig = ~in_sig;
    end
endmodule
module suppressed_warning_mod (
    input  logic [3:0] in_a,
    output logic [1:0] out_b
);
    /* verilator lint_off WIDTH */  
    assign out_b = in_a;            
    /* verilator lint_on WIDTH  */
endmodule
module unoptimized_expression_mod (
    input  logic [7:0] in_val,
    output logic [7:0] out_val
);
    assign out_val = (in_val & 8'hFF) | 8'h00;
endmodule
