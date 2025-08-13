module m_tristate_basic (
    input  logic din,
    input  logic en,
    inout  wire  pin,
    output logic dout
);
    assign pin  = en ? din : 1'bz;   
    assign dout = pin;               
endmodule
module m_bufif1_demo (
    input  wire data,
    input  wire enable,
    output wire y
);
    bufif1 (y, data, enable);        
endmodule
module m_bufif0_demo (
    input  wire data,
    input  wire enable_n,
    output wire y
);
    bufif0 (y, data, enable_n);      
endmodule
module m_concat_slice (
    input  logic [1:0] in,
    input  logic       en,
    inout  wire  [3:0] bus,
    output logic [3:0] dout
);
    assign bus = en ? {2'b00, in} : 4'bzzzz;        
    assign dout = {bus[0], bus[2], bus[3], bus[1]}; 
endmodule
module m_pullup_demo (
    input  wire driver,
    output wire out
);
    wire w;
    pullup (w);                          
    assign w = driver ? 1'b0 : 1'bz;     
    assign out = w;
endmodule
module m_pulldown_demo (
    input  wire driver,
    output wire out
);
    wire w;
    pulldown (w);                        
    assign w = driver ? 1'b1 : 1'bz;     
    assign out = w;
endmodule
module m_wor_net (
    input  wire a,
    input  wire b,
    output wor  out
);
    assign out = a;      
    assign out = b;      
endmodule
module m_wand_net (
    input  wire a,
    input  wire b,
    output wand out
);
    assign out = a;      
    assign out = b;      
endmodule
module m_strength_assign (
    input  wire in0,
    input  wire in1,
    output wire w
);
    wire w_internal;
    assign (strong1, weak0) w_internal = in0; 
    assign (weak1,  weak0)  w_internal = in1; 
    assign w = w_internal;
endmodule
module m_caseeq_demo (
    input  logic in,
    output logic eq,
    output logic neq
);
    logic tri_sig = 1'bz;
    assign eq  = (in === tri_sig); 
    assign neq = (in !== tri_sig); 
endmodule
module m_countones_demo (
    input  logic [7:0] vector_in,
    output logic [3:0] ones_count
);
    assign ones_count = $countones(vector_in); 
endmodule
module m_array_sel_demo (
    input  logic [7:0] din,
    input  logic       en,
    inout  wire  [7:0] bus,
    output logic       selected
);
    assign bus      = en ? din : 8'bzzzz_zzzz; 
    assign selected = bus[3];                  
endmodule
