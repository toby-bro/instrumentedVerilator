module bit_select_ops (
    input  logic [7:0] data_in,
    input  logic [3:0] idx,
    output logic       bit_out,
    output logic [7:0] data_out
);
    logic [7:0] vector_reg;
    always_comb begin
        vector_reg      = data_in;
        vector_reg[idx] = ~data_in[0];   
        data_out        = vector_reg;    
        bit_out         = vector_reg[idx]; 
    end
endmodule
module array_select_ops (
    input  logic        clk,
    input  logic [7:0]  byte_in,
    input  logic [1:0]  arr_idx,
    output logic [7:0]  byte_out
);
    logic [7:0] mem [0:3];               
    always_ff @(posedge clk) begin
        mem[arr_idx] <= byte_in;         
    end
    assign byte_out = mem[arr_idx];      
endmodule
module equality_ops (
    input  logic [3:0] in_a,
    output logic       eq_case,
    output logic       neq_case
);
    assign eq_case  = (in_a === 4'bx1x0); 
    assign neq_case = (in_a !== 4'bx1x0); 
endmodule
module wildcard_ops (
    input  logic [3:0] in_b,
    output logic       eq_wild,
    output logic       neq_wild
);
    assign eq_wild  = (in_b ==? 4'b1x0x); 
    assign neq_wild = (in_b !=? 4'b1x0x); 
endmodule
module isunknown_ops (
    input  logic [3:0] in_c,
    output logic       is_un
);
    assign is_un = $isunknown(in_c);     
endmodule
module countbits_ops (
    input  logic [7:0] in_d,
    output logic [3:0] cnt
);
    assign cnt = $countbits(in_d, 1'b1, 1'bx);
endmodule
module x_constant_ops (
    input  logic       dummy_in,
    output logic [4:0] out_x
);
    assign out_x = 5'bx1x0z;             
endmodule
module wire_assign_ops (
    input  logic [3:0] a,
    output logic [3:0] y
);
    wire [3:0] tmp;
    assign tmp = a & 4'bx1x0;            
    assign y   = tmp;
endmodule
