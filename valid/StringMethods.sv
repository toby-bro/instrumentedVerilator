module len_mod(input  logic        in_sig,
               output logic [31:0] out_len);
    localparam string str   = "verilator";
    localparam int    len_v = str.len();
    assign out_len = len_v;
endmodule
module putc_getc_mod(input  logic [7:0] in_dummy,
                     output logic [7:0] out_char);
    function automatic byte change_char();
        string s = "abc";
        s.putc(1, "Z");
        return s.getc(1);
    endfunction
    localparam byte ch = change_char();
    assign out_char = ch;
endmodule
module upper_lower_compare_mod(input  logic        in_stb,
                               output logic [31:0] cmp_res);
    localparam string base   = "hello";
    localparam string up     = base.toupper();
    localparam int    cmp1   = up.icompare("HELLO");
    localparam int    cmp2   = up.compare("HELLO");
    assign cmp_res = cmp1 + cmp2;
endmodule
module substr_mod(input  logic        in_val,
                  output logic [31:0] sub_len);
    localparam string sentence = "SystemVerilog";
    localparam string subpart  = sentence.substr(6, 12); 
    localparam int    l        = subpart.len();
    assign sub_len = l;
endmodule
module atoi_mod(input  logic        en,
                output logic [31:0] sum_out);
    localparam string s_dec = "123";
    localparam string s_hex = "7B";
    localparam string s_oct = "173";
    localparam string s_bin = "1111011";
    localparam int v_dec = s_dec.atoi();
    localparam int v_hex = s_hex.atohex();
    localparam int v_oct = s_oct.atooct();
    localparam int v_bin = s_bin.atobin();
    localparam int total = v_dec + v_hex + v_oct + v_bin;
    assign sum_out = total;
endmodule
module itoa_mod(input  logic        clk,
                output logic [31:0] len_total);
    function automatic int do_conv();
        string str_dec = "";
        string str_hex = "";
        string str_oct = "";
        string str_bin = "";
        int value = 255;
        str_dec.itoa(value);
        str_hex.hextoa(value);
        str_oct.octtoa(value);
        str_bin.bintoa(value);
        return str_dec.len() + str_hex.len() + str_oct.len() + str_bin.len();
    endfunction
    localparam int conv_len = do_conv();
    assign len_total = conv_len;
endmodule
module real_mod(input  logic        trig,
                output logic [31:0] len_real_str);
    function automatic int real_ops();
        string s = "3.25";
        real r_val = s.atoreal();
        string out_str = "";
        out_str.realtoa(r_val);
        return out_str.len();
    endfunction
    localparam int rl = real_ops();
    assign len_real_str = rl;
endmodule
