module const_table_8x32 (
    input  logic [4:0] idx,
    output logic [7:0] data
);
    localparam logic [7:0] TABLE [0:31] = '{
        8'h00, 8'h01, 8'h02, 8'h03, 8'h04, 8'h05, 8'h06, 8'h07,
        8'h08, 8'h09, 8'h0A, 8'h0B, 8'h0C, 8'h0D, 8'h0E, 8'h0F,
        8'h10, 8'h11, 8'h12, 8'h13, 8'h14, 8'h15, 8'h16, 8'h17,
        8'h18, 8'h19, 8'h1A, 8'h1B, 8'h1C, 8'h1D, 8'h1E, 8'h1F
    };
    assign data = TABLE[idx];
endmodule
module string_constant (
    input  logic sel,
    output logic [7:0] char_out
);
    localparam logic [7:0] MSG [0:10] = '{
        8'h56, 8'h33, 8'h43, 8'h6F, 8'h6E, 8'h73, 8'h74, 8'h50, 8'h6F, 8'h6F, 8'h6C
    };
    assign char_out = sel ? MSG[3] : MSG[0];
endmodule
module const_multi_dim (
    input  logic [1:0] a,
    input  logic [1:0] b,
    output logic [3:0] y
);
    localparam logic [3:0] MD_TABLE [0:3][0:3] = '{
        '{4'h0, 4'h1, 4'h2, 4'h3},
        '{4'h4, 4'h5, 4'h6, 4'h7},
        '{4'h8, 4'h9, 4'hA, 4'hB},
        '{4'hC, 4'hD, 4'hE, 4'hF}
    };
    assign y = MD_TABLE[a][b];
endmodule
module wide_const (
    input  logic sel,
    output logic [255:0] value_out
);
    localparam logic [255:0] WIDE_VALUE = 256'h0123_4567_89AB_CDEF_FEDC_BA98_7654_3210_0F0E_0D0C_0B0A_0908_0706_0504_0302_0100;
    assign value_out = sel ? WIDE_VALUE : ~WIDE_VALUE;
endmodule
module struct_const (
    input  logic en,
    output logic [11:0] packed_out
);
    typedef struct packed {
        logic [3:0] a;
        logic [7:0] b;
    } s_t;
    localparam s_t CONST_STRUCT = '{a:4'hA, b:8'h5A};
    assign packed_out = en ? {4'h0, 8'h00} : {CONST_STRUCT.a, CONST_STRUCT.b};
endmodule
module enum_const (
    input  logic clk,
    input  logic rst_n,
    output logic done
);
    typedef enum logic [1:0] {IDLE = 2'd0, RUN = 2'd1, DONE = 2'd2} state_e;
    localparam state_e INIT_ST = IDLE;
    state_e state_q;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state_q <= INIT_ST;
        end else begin
            state_q <= DONE;
        end
    end
    assign done = (state_q == DONE);
endmodule
module big_const_table (
    input  logic [7:0] idx,
    output logic [31:0] data_out
);
    localparam logic [31:0] BIG_TAB [0:255] = '{default:32'hDEAD_BEEF};
    assign data_out = BIG_TAB[idx];
endmodule
