`default_nettype none
module array_dir_mismatch(
    input  logic [7:0] in_bus [3:0],   
    output logic [7:0] out_bus [0:3]   
);
    always_comb begin
        out_bus = in_bus;               
    end
endmodule
module array_conditional(
    input  logic        select,
    input  logic [7:0]  arr0 [0:3],
    input  logic [7:0]  arr1 [0:3],
    output logic [7:0]  arr_out [0:3]
);
    always_comb begin
        arr_out = select ? arr0 : arr1; 
    end
endmodule
module array_equality(
    input  logic [7:0] arrA [0:3],
    input  logic [7:0] arrB [0:3],
    output logic       eq_out
);
    assign eq_out = (arrA == arrB);     
endmodule
module array_inequality(
    input  logic [7:0] arrA [0:3],
    input  logic [7:0] arrB [0:3],
    output logic       neq_out
);
    assign neq_out = (arrA != arrB);    
endmodule
module array_const(
    input  logic [7:0] in_bus [0:3],
    output logic [7:0] out_bus   [0:3],
    output logic [7:0] const_bus [0:3]
);
    localparam logic [7:0] CONST_ARR [0:3] = '{8'h11, 8'h22, 8'h33, 8'h44};
    always_comb begin
        out_bus   = in_bus;             
        const_bus = CONST_ARR;          
    end
endmodule
module struct_array(
    input  logic [3:0] in_x [0:1],
    input  logic       in_y [0:1],
    output logic [3:0] out_x [0:1],
    output logic       out_y [0:1]
);
    typedef struct packed {
        logic [3:0] x;
        logic       y;
    } my_t;
    my_t src [0:1];
    my_t dst [0:1];
    always_comb begin
        src[0].x = in_x[0];
        src[0].y = in_y[0];
        src[1].x = in_x[1];
        src[1].y = in_y[1];
        dst = src;
        out_x[0] = dst[0].x;
        out_x[1] = dst[1].x;
        out_y[0] = dst[0].y;
        out_y[1] = dst[1].y;
    end
endmodule
module array_slice_sel(
    input  logic [7:0] in_bus [0:3],
    output logic [7:0] elem1
);
    assign elem1 = in_bus[1];           
endmodule
module two_d_array_assign(
    input  logic [7:0] in2d  [0:1][0:1], 
    output logic [7:0] out1d [0:1]
);
    always_comb begin
        out1d[0] = in2d[0][0];
        out1d[1] = in2d[1][0];
    end
endmodule
`default_nettype wire
