module bits_example(
    input  logic [15:0] in_bus,
    output logic [31:0] bits_out
);
    typedef union packed {logic [7:0] a; logic [7:0] b;} u_t;
    localparam int BITS_VECTOR = $bits(logic [31:0]);
    localparam int BITS_UNION  = $bits(u_t);
    localparam int BITS_SIMPLE = $bits(bit [3:0]);
    always_comb begin
        bits_out = $bits(in_bus) + BITS_VECTOR + BITS_UNION + BITS_SIMPLE;
    end
endmodule
module array_bounds_example(
    input  logic sel,
    output logic [31:0] low_o,
    output logic [31:0] high_o,
    output logic [31:0] left_o,
    output logic [31:0] right_o,
    output logic [31:0] size_o,
    output logic [31:0] inc_o
);
    logic [3:0] asc_arr [0:7];
    logic [3:0] dsc_arr [7:0];
    always_comb begin
        low_o   = $low (asc_arr);
        high_o  = $high(asc_arr);
        left_o  = $left(asc_arr);
        right_o = $right(asc_arr);
        size_o  = $size(asc_arr);
        inc_o   = $increment(dsc_arr);
    end
endmodule
module dimensions_example(
    input  logic clk,
    output logic [31:0] dims_o
);
    logic [7:0] md_arr [0:1][0:2];
    localparam int TOTAL_DIMS = $dimensions(md_arr);
`ifndef VERILATOR
    localparam int UNPACKED_DIMS = $unpacked_dimensions(md_arr);
`else
    localparam int UNPACKED_DIMS = 0;
`endif
    always_comb dims_o = TOTAL_DIMS + UNPACKED_DIMS;
endmodule
`ifndef VERILATOR
module typename_example(
    input  logic dummy_in,
    output string type_name_out
);
    localparam string NAME_CONST = $typename(logic signed [3:0][7:0]);
    always_comb type_name_out = NAME_CONST;
endmodule
module isunbounded_example(
    input  logic trigger,
    output logic flag_out
);
    parameter int UNB_PARAM[] = '{1, 2, 3};
    always_comb flag_out = $isunbounded(UNB_PARAM);
endmodule
`endif
