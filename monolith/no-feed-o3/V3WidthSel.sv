//=========================================================
module bit_select_mod (
    input  logic [31:0] in_bus,
    input  logic [4:0]  index,
    output logic        out_bit
);
    assign out_bit = in_bus[index];
endmodule
//=========================================================
module range_select_mod (
    input  logic [31:0] in_bus,
    output logic [7:0]  out_vec
);
    assign out_vec = in_bus[15:8];
endmodule
//=========================================================
module plus_select_mod #(
    parameter WIDTH = 8
) (
    input  logic [31:0] in_bus,
    input  logic [4:0]  lsb,
    output logic [WIDTH-1:0] out_vec
);
    assign out_vec = in_bus[lsb +: WIDTH];
endmodule
//=========================================================
module minus_select_mod #(
    parameter WIDTH = 8
) (
    input  logic [31:0] in_bus,
    input  logic [4:0]  msb,
    output logic [WIDTH-1:0] out_vec
);
    assign out_vec = in_bus[msb -: WIDTH];
endmodule
//=========================================================
module unpacked_array_sel_mod (
    input  logic [1:0] index,
    output logic [7:0] out_byte
);
    localparam logic [7:0] CONST_ARR [0:3] = '{8'h11, 8'h22, 8'h33, 8'h44};
    assign out_byte = CONST_ARR[index];
endmodule
//=========================================================
module packed_array_sel_mod (
    input  logic [1:0] sel,
    output logic [7:0] out_byte
);
    localparam logic [0:3][7:0] PACKED_CONST = '{8'hAA, 8'hBB, 8'hCC, 8'hDD};
    assign out_byte = PACKED_CONST[sel];
endmodule
//=========================================================
module struct_bit_sel_mod (
    input  logic [4:0] sel_bit,
    output logic       out_bit
);
    typedef struct packed {
        logic [7:0] a;
        logic [7:0] b;
        logic [7:0] c;
    } my_t;
    localparam my_t SVAL = '{a:8'h12, b:8'h34, c:8'h56};
    assign out_bit = SVAL[sel_bit];
endmodule
//=========================================================
module string_sel_mod (
    input  logic [4:0] idx,
    output logic [7:0] out_char
);
    localparam string STR = "Hello, Verilator!";
    assign out_char = STR[idx];
endmodule
//=========================================================
module queue_sel_mod (
    input  logic dummy_in,   
    output logic [7:0] out_byte
);
    byte unsigned q[$] = {8'h11, 8'h22, 8'h33, 8'h44};
    always_comb begin
        out_byte = q[$ - 1];
    end
endmodule
//=========================================================
module assoc_array_sel_mod (
    input  int  index,
    output logic [7:0] out_byte
);
    logic [7:0] assoc[int] = '{0:8'h55, 5:8'hAA, default:8'h00};
    always_comb begin
        out_byte = assoc[index];
    end
endmodule
