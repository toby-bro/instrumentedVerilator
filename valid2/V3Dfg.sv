module dfg_arithmetic #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] in_a,
    input  logic [WIDTH-1:0] in_b,
    output logic [(2*WIDTH)-1:0] out_result
);
    always_comb begin
        out_result = (in_a * in_b) + (in_a << 2) - (in_b >> 1);
    end
endmodule
module dfg_bitwise_select (
    input  logic [15:0] data_in,
    input  logic [3:0]  index,
    output logic [3:0]  part_sel
);
    logic [15:0] shifted;
    assign shifted = {data_in[7:0], data_in[15:8]};  
    always_comb begin
        part_sel = shifted[index +: 4];               
    end
endmodule
module dfg_mux (
    input  logic        sel,
    input  logic [7:0]  a,
    input  logic [7:0]  b,
    output logic [7:0]  y
);
    assign y = sel ? a : b;                           
endmodule
module dfg_concat_pack (
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic [7:0] y
);
    assign y = {a, b};                                
endmodule
module dfg_array_builder (
    input  logic [7:0] in0,
    input  logic [7:0] in1,
    output logic [7:0] out0,
    output logic [7:0] out1
);
    logic [7:0] my_arr [0:1];                         
    always_comb begin
        my_arr = '{in0, in1};                         
    end
    assign out0 = my_arr[0];
    assign out1 = my_arr[1];
endmodule
