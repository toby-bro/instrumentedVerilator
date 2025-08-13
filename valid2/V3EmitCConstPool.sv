typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;
module cp_newOutCFile(
    input  logic [1:0]  sel,
    output logic [31:0] data_out
);
    localparam logic [31:0] CONST_POOL [0:3] = '{
        32'hDEADBEEF,
        32'hCAFEBABE,
        32'h0BAD_F00D,
        32'hFEED_FACE
    };
    assign data_out = CONST_POOL[sel];
endmodule
module cp_maybeSplit(
    input  logic [7:0] addr,
    output logic [7:0] byte_out
);
    localparam logic [7:0] ROM [0:255] = '{
        default : 8'h00,
        0 : 8'hA5,
        1 : 8'h5A,
        2 : 8'h3C,
        3 : 8'hC3
    };
    assign byte_out = ROM[addr];
endmodule
module cp_emitVars(
    input  logic [3:0] row,
    input  logic [1:0] col,
    output logic [15:0] word_out
);
    localparam logic [15:0] TABLE [0:15][0:3] = '{
        '{16'h0001,16'h0002,16'h0003,16'h0004},
        '{16'h0011,16'h0012,16'h0013,16'h0014},
        '{16'h0021,16'h0022,16'h0023,16'h0024},
        '{16'h0031,16'h0032,16'h0033,16'h0034},
        '{16'h0041,16'h0042,16'h0043,16'h0044},
        '{16'h0051,16'h0052,16'h0053,16'h0054},
        '{16'h0061,16'h0062,16'h0063,16'h0064},
        '{16'h0071,16'h0072,16'h0073,16'h0074},
        '{16'h0081,16'h0082,16'h0083,16'h0084},
        '{16'h0091,16'h0092,16'h0093,16'h0094},
        '{16'h00A1,16'h00A2,16'h00A3,16'h00A4},
        '{16'h00B1,16'h00B2,16'h00B3,16'h00B4},
        '{16'h00C1,16'h00C2,16'h00C3,16'h00C4},
        '{16'h00D1,16'h00D2,16'h00D3,16'h00D4},
        '{16'h00E1,16'h00E2,16'h00E3,16'h00E4},
        '{16'h00F1,16'h00F2,16'h00F3,16'h00F4}
    };
    assign word_out = TABLE[row][col];
endmodule
module cp_lambdaSort(
    input  logic   sel,
    output pair_t  out_pair
);
    localparam pair_t PAIRS [0:1] = '{
        '{8'h12,8'h34},
        '{8'hAB,8'hCD}
    };
    assign out_pair = PAIRS[sel];
endmodule
module cp_visitConst(
    input  logic          enable,
    output logic [1023:0] wide_out
);
    localparam logic [1023:0] BIG_CONST = {256{4'hF}};
    assign wide_out = enable ? BIG_CONST : '0;
endmodule
module cp_constructorPool(
    input  logic       clk,
    input  logic       rst,
    output logic [31:0] id_out
);
    class dummy_c;
        bit [31:0] id;
        function new(bit [31:0] v); id = v; endfunction
    endclass
    dummy_c d;
    always_ff @(posedge clk) begin
        if (rst) begin
            id_out <= 32'h0;
        end else begin
            d = new(32'h1234_5678);
            id_out <= d.id;
        end
    end
endmodule
module cp_stats(
    input  logic [1:0] state_sel,
    output logic [3:0] stat_out
);
    typedef enum logic [3:0] {
        ST_IDLE = 4'd0,
        ST_RUN  = 4'd1,
        ST_DONE = 4'd2,
        ST_ERR  = 4'd3
    } state_e;
    localparam state_e STATES [0:3] = '{ST_IDLE, ST_RUN, ST_DONE, ST_ERR};
    assign stat_out = STATES[state_sel];
endmodule
module cp_rootEmit(
    input  logic        trig,
    output logic [63:0] mixed_out
);
    typedef union packed {
        logic [63:0] ui;
        struct packed { logic [31:0] lo; logic [31:0] hi; } s;
    } mix_u;
    localparam mix_u CONST_MIX = mix_u'(64'hDEADBEEF_CAFEF00D);
    assign mixed_out = trig ? CONST_MIX.ui : 64'h0;
endmodule
