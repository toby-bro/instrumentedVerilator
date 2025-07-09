class dummy_class;
    bit [31:0] data;
    function new(bit [31:0] d);
        data = d;
    endfunction
    function bit [31:0] get();
        return data;
    endfunction
endclass
module bin_literal_mod #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH+3:0] out
);
    localparam logic [3:0] BIN_CONST = 4'b1x0z;
    assign out = {BIN_CONST, in};
endmodule
module oct_literal_mod (
    input  logic [7:0] in,
    output logic [11:0] out
);
    localparam logic [11:0] OCT_CONST = 12'o17x;
    assign out = OCT_CONST ^ in;
endmodule
module decimal_literal_mod (
    input  logic  signed [15:0] in,
    output logic  signed [17:0] out
);
    localparam logic signed [7:0]  DEC_MIN     = -8'sd128;
    localparam logic        [31:0] DEC_UNKNOWN = 32'dx;
    assign out = DEC_MIN + in + DEC_UNKNOWN[7:0];
endmodule
module hex_literal_overflow_mod (
    input  logic [15:0] in,
    output logic [15:0] out
);
    localparam logic [3:0] SMALL_HEX = 4'hABC;
    assign out = in ^ {12'd0, SMALL_HEX};
endmodule
module unsized_literal_mod (
    input  logic [31:0] in,
    output logic [63:0] out
);
    localparam logic [63:0] BIG_HEX = 'hDEAD_BEEF_F00D_F00D;
    assign out = BIG_HEX | {32'd0, in};
endmodule
module huge_literal_mod (
    input  logic [3:0]  sel,
    output logic [1023:0] value
);
    localparam logic [1023:0] HUGE = 1024'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;
    always_comb begin
        case (sel)
            4'd0: value = HUGE;
            4'd1: value = HUGE >> 256;
            4'd2: value = HUGE >> 512;
            default: value = HUGE >> 768;
        endcase
    end
endmodule
module class_inst_mod (
    input  logic [31:0] in,
    output logic [31:0] out
);
    always_comb begin
        dummy_class inst = new(in);        
        out = inst.get();
    end
endmodule
