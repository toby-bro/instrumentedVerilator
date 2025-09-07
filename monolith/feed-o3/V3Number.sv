module numbers_basic (
    input  logic [3:0]  in_sig,
    output logic [3:0]  out_sig
);
    /* Basic constant numbers making Verilator exercise unsized, sized and 4-state digits */
    localparam logic         p_zero   = '0;           
    localparam logic         p_one    = '1;           
    localparam logic         p_unkX   = 'x;           
    localparam logic         p_unkZ   = 'z;           
    localparam logic [7:0]   p_hex    = 8'hA5;        
    localparam logic [31:0]  p_big    = 32'd2 ** 31;  
    localparam logic [15:0]  p_mixed  = 16'b1x0z_1x0z_1x0z_1x0z;  
    assign out_sig = in_sig;   
endmodule
module arithmetic_ops (
    input  logic [7:0] in_a,
    output logic [7:0] out_a
);
    /* Constant arithmetic – hits add, sub, mul, div, mod and power paths              */
    localparam logic [31:0] p_add  = 32'd123 + 32'd456;          
    localparam logic [31:0] p_sub  = 32'd1000 - 32'd321;         
    localparam logic [31:0] p_mul  = 32'd22   * 32'd11;          
    localparam logic [31:0] p_div  = 32'd1024 / 32'd8;           
    localparam logic [31:0] p_mod  = 32'd100  % 32'd33;          
    localparam logic [31:0] p_pow  = 32'd2 ** 8;                 
    assign out_a = in_a;     
endmodule
module shift_ops (
    input  logic [15:0] in_b,
    output logic [15:0] out_b
);
    /* Constant shifts (logical and arithmetic)                                         */
    localparam logic [15:0] p_sll = 16'h00FF << 4;            
    localparam logic [15:0] p_srl = 16'hFF00 >> 8;            
    localparam logic [15:0] p_sra = $signed(16'hF000) >>> 4;  
    assign out_b = in_b;
endmodule
module reduction_ops (
    input  logic in_c,
    output logic out_c
);
    /* Constant reductions to trigger opRedAnd / opRedOr / opRedXor                      */
    localparam logic red_or  = |8'b0001_0000;   
    localparam logic red_and = &8'b1111_1111;   
    localparam logic red_xor = ^8'b1010_1010;   
    assign out_c = in_c;
endmodule
module comparison_ops (
    input  logic [3:0] in_d,
    output logic [3:0] out_d
);
    /* Equality, case equality, wildcard equality and relational                        */
    localparam bit cmp_eq   = (8'hAA == 8'hAA);          
    localparam bit cmp_neq  = (8'h55 != 8'hAA);          
    localparam bit cmp_ceq  = (8'hFF === 8'hFF);         
    localparam bit cmp_cneq = (8'hF0 !== 8'hF1);         
    localparam bit cmp_gt   = (16'd200 >  16'd100);      
    localparam bit cmp_gte  = (16'd100 >= 16'd100);      
    localparam bit cmp_lt   = (16'd50  <  16'd60 );      
    localparam bit cmp_lte  = (16'd60  <= 16'd60 );      
    localparam bit cmp_wild = (8'hF0 ==? 8'hF?);         
    assign out_d = in_d;
endmodule
module concat_repl_stream (
    input  logic [7:0]  in_e,
    output logic [31:0] out_e
);
    /* Concatenation, replication and streaming concatenation                           */
    localparam logic [15:0] p_concat = {4'hA, 4'hB, 8'hC3};       
    localparam logic [15:0] p_repl   = {4{4'hE}};                
    localparam logic [15:0] p_stream_src  = 16'h1234;
    localparam logic [15:0] p_stream_dest = { << 8 { p_stream_src } };
    assign out_e = {in_e, in_e, in_e, in_e};  
endmodule
module real_ops (
    input  logic        clk,
    output logic [31:0] dummy
);
    /* Real (double) arithmetic to reach opAddD, opSubD, opMulD, opDivD, opPowD          */
    localparam real r_add = 1.5 + 2.25;          
    localparam real r_sub = 5.0 - 3.0;           
    localparam real r_mul = 2.0 * 4.0;           
    localparam real r_div = 3.0 / 2.0;           
    localparam real r_pow = 2.0 ** 3.0;          
    localparam int  r_int = int'(r_div);         
    assign dummy = 0;
endmodule
module string_ops (
    input  logic  gate,
    output logic  flag
);
    /* Constant string handling – concatenation, replication and comparisons            */
    localparam string s1   = "Hello";
    localparam string s2   = "World";
    localparam string s3   = {s1, " ", s2};          
    localparam string s4   = {3{s1}};                
    localparam bit    s_eq = ("abc" == "abc");       
    localparam bit    s_gt = ("def"  > "abc");       
    assign flag = gate;
endmodule
