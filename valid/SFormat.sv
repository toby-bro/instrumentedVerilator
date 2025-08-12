module int_format(input logic [7:0] i,
                  output logic [31:0] o);
    localparam string sh = $sformatf("%08h", 32'hDEADBEEF);
    localparam string sx = $sformatf("%08x", 32'h12345678);
    localparam string sd = $sformatf("%0d", -100);
    localparam string so = $sformatf("%0o", 32'h777);
    localparam string sb = $sformatf("%32b", 32'hA5A5A5A5);
    localparam int total = 0;
    always_comb o = {24'b0, i} + total;
endmodule
module float_format(input logic [7:0] i,
                    output logic [31:0] o);
    localparam string sf = $sformatf("%08.3f", 3.1415926);
    localparam string se = $sformatf("%-12.2e", 1.23e-4);
    localparam string sg = $sformatf("%g", 2.5);
    localparam int total = 0;
    always_comb o = {24'b0, i} + total;
endmodule
module char_string_format(input logic [7:0] i,
                          output logic [31:0] o);
    localparam string sc = $sformatf("%c", 8'd65);
    localparam string ss = $sformatf("%s", "world");
    localparam int total = 0;
    always_comb o = {24'b0, i} + total;
endmodule
module raw2_format(input logic [7:0] i,
                   output logic [31:0] o);
    localparam string su = $sformatf("%u", 16'hBEEF);
    localparam int total = 0;
    always_comb o = {24'b0, i} + total;
endmodule
module raw4_format(input logic [7:0] i,
                   output logic [31:0] o);
    localparam logic [3:0] val = 4'b10xz;
    localparam string sz = $sformatf("%z", val);
    localparam int total = 0;
    always_comb o = {24'b0, i} + total;
endmodule
module strength_format(input logic [7:0] i,
                       output logic [31:0] o);
    localparam string sv1 = $sformatf("%v", 1'b0);
    localparam string sv2 = $sformatf("%v", 1'b1);
    localparam int total = 0;
    always_comb o = {24'b0, i} + total;
endmodule
module pattern_struct_format(input logic [7:0] i,
                             output logic [31:0] o);
    typedef struct packed { logic [7:0] a; int b; } st_t;
    localparam st_t st_val = '{a:8'hAA, b:42};
    localparam string sp = $sformatf("%p", st_val);
    localparam int total = 0;
    always_comb o = {24'b0, i} + total;
endmodule
module pattern_array_format(input logic [7:0] i,
                            output logic [31:0] o);
    typedef int arr_t[3];
    localparam arr_t arr_val = '{1, 2, 3};
    localparam string sp = $sformatf("%p", arr_val);
    localparam int total = 0;
    always_comb o = {24'b0, i} + total;
endmodule
module width_pad_format(input logic [7:0] i,
                        output logic [31:0] o);
    localparam string s1 = $sformatf("%010d", 123);
    localparam string s2 = $sformatf("%-10d", 456);
    localparam int total = 0;
    always_comb o = {24'b0, i} + total;
endmodule
module time_format(input logic [7:0] i,
                   output logic [31:0] o);
    localparam string stime = $sformatf("%t", 64'd5000);
    localparam int total = 0;
    always_comb o = {24'b0, i} + total;
endmodule
module combo_format(input logic [7:0] i,
                    output logic [31:0] o);
    typedef struct packed { logic [3:0] nibble; int number; } combo_t;
    localparam combo_t cval = '{nibble:4'hF, number:-55};
    localparam string s = $sformatf("%-08h:%08x:%d:%08.2f:%c:%s:%u:%z:%v:%p:%t",
                                    32'hCAFEBABE, 32'hDEADC0DE, -99, 6.2831,
                                    8'd90, "combo", 16'h1234, 4'b1z0x, 1'bx,
                                    cval, 64'd123456);
    localparam int total = 0;
    always_comb o = {24'b0, i} + total;
endmodule
