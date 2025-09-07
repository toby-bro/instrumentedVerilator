//********************************************************************
//********************************************************************
//--------------------------------------------------------------------
module const_scalar #(parameter WIDTH = 32) (
    input  logic                 i_sel,
    output logic [WIDTH-1:0]     o_data
);
    const logic [WIDTH-1:0] CONST_A = 32'h12345678;
    const logic [WIDTH-1:0] CONST_B = 32'h87654321;
    assign o_data = i_sel ? CONST_A : CONST_B;
endmodule
//--------------------------------------------------------------------
module wide_const (
    input  logic i_en,
    output logic o_bit
);
    const logic [1023:0] BIG = 1024'hFFEEDDCCBBAA99887766554433221100FFEEDDCCBBAA99887766554433221100FFEEDDCCBBAA99887766554433221100FFEEDDCCBBAA99887766554433221100FFEEDDCCBBAA99887766554433221100FFEEDDCCBBAA99887766554433221100FFEEDDCCBBAA99887766554433221100FFEEDDCCBBAA99887766554433221100;
    assign o_bit = i_en & BIG[0];
endmodule
//--------------------------------------------------------------------
module const_array1d (
    input  logic  [3:0] addr,
    output logic  [7:0] data
);
    const logic [7:0] ROM [0:15] = '{
        8'h00, 8'h11, 8'h22, 8'h33,
        8'h44, 8'h55, 8'h66, 8'h77,
        8'h88, 8'h99, 8'hAA, 8'hBB,
        8'hCC, 8'hDD, 8'hEE, 8'hFF
    };
    assign data = ROM[addr];
endmodule
//--------------------------------------------------------------------
module const_array2d (
    input  logic [1:0] sel_row,
    input  logic [1:0] sel_col,
    output logic [3:0] value
);
    const logic [3:0] G [0:3][0:3] = '{
        '{4'd0 , 4'd1 , 4'd2 , 4'd3 },
        '{4'd4 , 4'd5 , 4'd6 , 4'd7 },
        '{4'd8 , 4'd9 , 4'd10, 4'd11},
        '{4'd12, 4'd13, 4'd14, 4'd15}
    };
    assign value = G[sel_row][sel_col];
endmodule
//--------------------------------------------------------------------
module const_string (
    input  logic      i_en,
    output logic [7:0] o_char
);
    const string MESSAGE = "HELLO Verilator!";
    const byte   CHAR0  = MESSAGE[0];
    assign o_char = i_en ? CHAR0 : 8'h00;
endmodule
//--------------------------------------------------------------------
module const_struct (
    input  logic sel,
    output logic [7:0] o
);
    typedef struct packed {
        logic [7:0] x;
        logic [7:0] y;
    } pair_t;
    const pair_t PAIRS [0:1] = '{
        '{8'hAA, 8'h55},
        '{8'hCC, 8'h33}
    };
    assign o = sel ? PAIRS[1].y : PAIRS[0].x;
endmodule
