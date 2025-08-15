module m_slice_pass  
(
    input  logic [7:0] in_arr  [0:3],
    output logic [7:0] out_arr [0:3]
);
    always_comb begin
        out_arr = in_arr;          
    end
endmodule
module m_slice_reverse  
(
    input  logic [7:0] in_arr  [3:0],  
    output logic [7:0] out_arr [0:3]   
);
    always_comb begin
        out_arr = in_arr;          
    end
endmodule
module m_eq_compare  
(
    input  logic [7:0] a [0:3],
    input  logic [7:0] b [0:3],
    output logic       eq
);
    always_comb begin
        eq = (a == b);             
    end
endmodule
module m_neq_compare  
(
    input  logic [7:0] a [0:3],
    input  logic [7:0] b [0:3],
    output logic       neq
);
    always_comb begin
        neq = (a != b);            
    end
endmodule
module m_cond_select  
(
    input  logic sel,
    input  logic [7:0] a [0:3],
    input  logic [7:0] b [0:3],
    output logic [7:0] y [0:3]
);
    always_comb begin
        y = sel ? a : b;           
    end
endmodule
module m_case_eq  
(
    input  logic [7:0] a [0:3],
    input  logic [7:0] b [0:3],
    output logic       ceq
);
    always_comb begin
        ceq = (a === b);           
    end
endmodule
module m_const_array  
(
    input  logic dummy,                 
    output logic [7:0] const_out [0:3]
);
    always_comb begin
        const_out = '{8'hAA, 8'hBB, 8'hCC, 8'hDD};  
    end
endmodule
