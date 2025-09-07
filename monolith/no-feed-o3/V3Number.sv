module logic_ops_mod(input  logic [31:0] a,
                      input  logic [31:0] b,
                      output logic [31:0] y_and,
                      output logic [31:0] y_or,
                      output logic [31:0] y_xor,
                      output logic [31:0] y_nand);
    always_comb begin
        y_and  =  a & b;
        y_or   =  a | b;
        y_xor  =  a ^ b;
        y_nand = ~(a & b);
    end
endmodule
module reduction_mod(input  logic [15:0] in_vec,
                     output logic any_set,
                     output logic all_set,
                     output logic parity);
    always_comb begin
        any_set = |in_vec;
        all_set = &in_vec;
        parity  = ^in_vec;
    end
endmodule
module shift_pow_mod(input  logic signed [31:0] val,
                     input  logic [5:0] shamt,
                     output logic signed [63:0] r_shift,
                     output logic signed [63:0] l_shift,
                     output logic signed [63:0] pow3);
    assign r_shift = val >>> shamt;
    assign l_shift = val <<< shamt;
    assign pow3    = val ** 3;
endmodule
module concat_repl_mod(input  logic [7:0] a,
                       input  logic [7:0] b,
                       output logic [31:0] o_concat,
                       output logic [31:0] o_repl);
    assign o_concat = {a, b, 8'hAA, 8'h55};
    assign o_repl   = {4{a}};
endmodule
module stream_mod(input  logic [15:0] din,
                  output logic [15:0] stream_rev);
    assign stream_rev = {<<{2{din}}};
endmodule
module compare_mod(input  logic [31:0] a,
                   input  logic [31:0] b,
                   output logic eq,
                   output logic neq,
                   output logic ceq,
                   output logic cneq,
                   output logic weq,
                   output logic wneq,
                   output logic gt,
                   output logic gte,
                   output logic lt,
                   output logic lte);
    assign eq   = (a ==  b);
    assign neq  = (a !=  b);
    assign ceq  = (a === b);
    assign cneq = (a !== b);
    assign weq  = (a ==? b);
    assign wneq = (a !=? b);
    assign gt   = (a  >  b);
    assign gte  = (a >=  b);
    assign lt   = (a  <  b);
    assign lte  = (a <=  b);
endmodule
module string_mod #(parameter string STR = "HelloWorld")
                   (output logic [31:0] len,
                    output logic [31:0] sublen,
                    output logic [7:0]  ch0,
                    output logic        equal_test);
    localparam int LENP          = STR.len();
    localparam string LOWER      = STR.tolower();
    localparam int SUBLENP       = STR.substr(1,3).len();
    localparam byte CH           = STR.getc(0);
    localparam bit  EQCMP        = (STR == LOWER);
    assign len        = LENP;
    assign sublen     = SUBLENP;
    assign ch0        = CH;
    assign equal_test = EQCMP;
endmodule
module real_conv_mod(input  logic [31:0] int_in,
                     output real         real_out,
                     output logic [31:0] int_out);
    assign real_out = $itor(int_in);
    assign int_out  = $rtoi(real_out);
endmodule
module dynamic_sel_mod(input  logic [63:0] bus,
                       input  logic [5:0] index,
                       output logic [7:0] part);
    assign part = bus[index +: 8];
endmodule
