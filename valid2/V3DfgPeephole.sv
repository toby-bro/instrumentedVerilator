//======================================================
//======================================================
//------------------------------------------------------
//------------------------------------------------------
module ph_logic_combo #(
    parameter WIDTH = 32
) (
    input  logic [WIDTH-1:0]  in_a,
    input  logic [WIDTH-1:0]  in_b,
    output logic [WIDTH-1:0]  out_y
);
    logic [WIDTH-1:0] t0, t1, t2, t3;
    assign t0 = in_a & {WIDTH{1'b1}};                
    assign t1 = t0  & (in_a & in_b);                 
    assign t2 = (~in_a) & (~in_b);                   
    assign t3 = t2 | (32'h0000_0000 | in_b);         
    assign out_y = (t1 ^ t3) ^ 32'hFFFF_FFFF;        
endmodule
//------------------------------------------------------
//------------------------------------------------------
module ph_concat_shift_sel (
    input  logic [15:0] in_data,
    input  logic [3:0]  in_shift,
    output logic [15:0] out_sel
);
    logic [19:0] zext  = {4'h0, in_data};            
    logic [35:0] mix   = {zext, in_data};            
    logic [35:0] shft  = mix >> {in_shift, 2'b00};   
    logic [23:0] slice = shft[31:8];                 
    logic [15:0] tmp   = slice[23:8];                
    assign out_sel = tmp;
endmodule
//------------------------------------------------------
//------------------------------------------------------
module ph_reduction (
    input  logic [7:0] in_a,
    input  logic [7:0] in_b,
    output logic       out_y
);
    logic red_and  = &in_a;      
    logic red_or   = |in_b;      
    logic red_xor  = ^{in_a, in_b}; 
    assign out_y = (red_and & red_or) ^ red_xor; 
endmodule
//------------------------------------------------------
//------------------------------------------------------
module ph_replicate (
    input  logic in_bit,
    output logic [7:0] out_bus
);
    assign out_bus = {8{in_bit}} ^ 8'hFF;            
endmodule
//------------------------------------------------------
//------------------------------------------------------
module ph_extend (
    input  logic  [7:0] in_small,
    output logic [15:0] out_zero,
    output logic [15:0] out_sign
);
    assign out_zero = 16'(in_small);                 
    assign out_sign = $signed(in_small);             
endmodule
//------------------------------------------------------
//------------------------------------------------------
module ph_conditional (
    input  logic        sel1,
    input  logic        sel2,
    input  logic [3:0]  in_a,
    input  logic [3:0]  in_b,
    output logic [3:0]  out_y
);
    logic [3:0] inc_a = in_a + 4'd1;                 
    logic [3:0] dec_b = in_b - 4'd1;                 
    assign out_y = sel1 ? (sel2 ? in_a : in_b)
                        : (sel2 ? inc_a : dec_b);    
endmodule
//------------------------------------------------------
//------------------------------------------------------
module ph_distributive (
    input  logic [15:0] x,
    input  logic [15:0] y,
    input  logic [15:0] z,
    output logic [15:0] out_y
);
    logic [15:0] a = x & y;
    logic [15:0] b = x & z;
    assign out_y = a | b;                            
endmodule
//------------------------------------------------------
//------------------------------------------------------
module ph_shift_rhs (
    input  logic [31:0] data,
    input  logic [3:0]  shamt,
    output logic [31:0] out_l,
    output logic [31:0] out_r
);
    logic [7:0] rhs_ext = {4'h0, shamt};             
    assign out_l = data << rhs_ext;                  
    assign out_r = data >> rhs_ext;                  
endmodule
//------------------------------------------------------
//------------------------------------------------------
module ph_onehot (
    input  logic [7:0] in_bus,
    output logic [7:0] out_hot,
    output logic [7:0] out_hot0
);
    assign out_hot  = 8'(in_bus == (in_bus & -in_bus));  
    assign out_hot0 = 8'(in_bus == 8'd0) ? 8'd1 : out_hot; 
endmodule
//------------------------------------------------------
//------------------------------------------------------
module ph_array_sel (
    input  logic [7:0] bus_in [0:3],
    output logic [7:0] out_const,
    input  logic [1:0] dyn_idx,
    output logic [7:0] out_dyn
);
    assign out_const = bus_in[2];                    
    assign out_dyn   = bus_in[dyn_idx];              
endmodule
