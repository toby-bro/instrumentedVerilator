module fmt_int (
    input  logic  in_sig,
    output string formatted
);
    localparam int  hex_val = 32'hDEADBEEF;
    localparam int  dec_val = -123456;
    localparam int  oct_val = 32'd511;
    localparam int  bin_val = 8'b10110011;
    localparam time my_time = 64'd123456789;
    localparam string msg = $sformatf("%% H:%08h D:%-10d O:%o B:%b T:%t %%",
                                      hex_val, dec_val, oct_val, bin_val, my_time);
    always_comb formatted = msg;
endmodule
module fmt_float (
    input  logic  dummy,
    output string formatted
);
    localparam real pi = 3.141592653589793;
    localparam string msg = $sformatf("PI_e:%12.5e PI_f:%10.3f PI_g:%g",
                                      pi, pi, pi);
    always_comb formatted = msg;
endmodule
module fmt_char_str (
    input  logic  dummy,
    output string formatted
);
    localparam int    charA = 65;          
    localparam string base  = "hello";
    localparam string msg = $sformatf("Char:%c|String:%-10s|%%",
                                      charA, base);
    always_comb formatted = msg;
endmodule
module fmt_raw_strength (
    input  logic  dummy,
    output string formatted
);
    localparam logic [15:0] raw_val = 16'hABCD;
    localparam logic [3:0]  str_val = 4'b1x0z;
    localparam logic [31:0] unk_val = 32'hX;
    localparam string part1 = $sformatf("U:%u Z:%z V:%v",
                                        raw_val, raw_val, str_val);
    localparam string part2 = $sformatf("Z2:%z", unk_val);
    localparam string msg   = {part1, " | ", part2};
    always_comb formatted = msg;
endmodule
module fmt_pattern_struct (
    input  logic  dummy,
    output string formatted
);
    typedef struct packed {
        logic [3:0] nib;
        logic [1:0] flag;
    } packed_s_t;
    localparam packed_s_t pk = '{nib:4'hA, flag:2'b10};
    typedef enum logic [1:0] {ZERO = 0, ONE = 1, TWO = 2} my_enum_t;
    localparam my_enum_t ev = TWO;
    localparam int arr [0:2] = '{1, 2, 3};
    localparam string s_struct = $sformatf("PK:%p", pk);
    localparam string s_enum   = $sformatf("EV:%p", ev);
    localparam string s_arr    = $sformatf("AR:%p", arr);
    localparam string msg      = {s_struct, " ", s_enum, " ", s_arr};
    always_comb formatted = msg;
endmodule
