module cmp_width #(parameter W = 8) (
    input  logic signed [W-1:0] in1,
    input  logic        [W-1:0] in2,
    output logic                eq_u,
    output logic                gt_u,
    output logic                lt_s,
    output logic                ge_s
);
    assign eq_u = (in1 == in2);                 
    assign gt_u = (in1  > in2);                 
    assign lt_s = ($signed(in1) <  $signed(in2)); 
    assign ge_s = ($signed(in1) >= $signed(in2)); 
endmodule
module logic_reduce (
    input  logic [15:0] a,
    input  logic [15:0] b,
    output logic        red_and,
    output logic        red_or,
    output logic        log_and,
    output logic        log_or
);
    assign red_and = &a;                
    assign red_or  = |b;                
    assign log_and = (a!=16'd0) && (b!=16'd0); 
    assign log_or  = (a!=16'd0) || (b!=16'd0); 
endmodule
module real_math (
    input  real a_r,
    input  real b_r,
    output real sum_r,
    output real mul_r
);
    assign sum_r = a_r + b_r;           
    assign mul_r = a_r * b_r;           
endmodule
module shift_ops (
    input  logic [31:0] data,
    input  logic  [4:0] shamt,
    output logic [31:0] shl,
    output logic [31:0] shr,
    output logic [31:0] sar
);
    assign shl = data <<< shamt;                      
    assign shr = data >>  shamt;                      
    assign sar = $signed(data) >>> shamt;             
endmodule
module concat_rep (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [31:0] concat_out,
    output logic [15:0] rep_out
);
    assign concat_out = {a, b, 8'hAA, 8'h55}; 
    assign rep_out    = {4{a[3:0]}};           
endmodule
module conditional_test (
    input  logic        sel,
    input  logic [7:0]  x,
    input  logic [7:0]  y,
    output logic [7:0]  z
);
    assign z = sel ? x : y;                   
endmodule
module pattern_struct (
    input  logic [3:0] in_a,
    input  logic [3:0] in_b,
    output logic [7:0] packed_out
);
    typedef struct packed {
        logic [3:0] a;
        logic [3:0] b;
    } mystruct_t;
    mystruct_t temp_struct = '{a: in_a, b: in_b}; 
    assign packed_out = temp_struct;              
endmodule
module enum_test (
    input  logic [1:0] s1,
    input  logic [1:0] s2,
    output logic       eq,
    output logic       gt
);
    typedef enum logic [1:0] {IDLE=2'd0, RUN=2'd1, STOP=2'd2} state_t;
    state_t st1 = state_t'(s1);
    state_t st2 = state_t'(s2);
    assign eq = (st1 == st2);           
    assign gt = (st1  > st2);           
endmodule
module class_test (
    input  logic trigger,
    output logic [7:0] out
);
    class simple;
        rand logic [7:0] d;
    endclass
    always_comb begin
        simple s = new();
        out = s.d;                      
    end
endmodule
